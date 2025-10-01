import os
import re
import sys
from datetime import datetime
import google.generativeai as genai
from github import Github, Auth

# --- Constants ---
MAX_DIFF_TOKENS = 1_500_000
COMMENT_IDENTIFIER = "<!-- gemini-pr-summary -->"
SORRY_KEYWORDS = ["theorem", "def", "lemma", "instance", "example", "corollary", "proposition"]

# --- AI Summary Generation ---
def generate_ai_summary(diff):
    """Generates a concise, high-level summary of a git diff using the Gemini API."""
    if len(diff) > MAX_DIFF_TOKENS:
        diff = diff[:MAX_DIFF_TOKENS]
        truncated = True
    else:
        truncated = False

    model = genai.GenerativeModel('gemini-2.5-pro')
    prompt = f"""
    Please provide a concise, high-level summary of the following git diff.
    Focus on the key changes and their purpose. Do not describe the changes line-by-line.
    Use bullet points for clarity if needed.

    Diff:
    {diff}
    """
    try:
        response = model.generate_content(prompt)
        return response.text, truncated
    except Exception as e:
        return f"Error generating summary: {e}", False

# --- Diff Analysis ---
def analyze_diff(diff):
    """Parses a git diff to extract statistics and track 'sorry's."""
    files_changed = set()
    lines_added = 0
    lines_removed = 0
    added_sorries = []
    removed_sorries = []
    affected_sorries = []

    current_file = ""
    old_line_num = 0
    new_line_num = 0

    # Regex to capture file paths from the diff header
    file_path_regex = re.compile(r'diff --git a/(.+) b/(.+)')
    # Regex to capture line numbers from the hunk header
    hunk_header_regex = re.compile(r'@@ -(\d+),?(\d*) \+(\d+),?(\d*) @@')

    # First pass: collect all added and removed sorries with their context
    raw_added = []
    raw_removed = []

    for line in diff.splitlines():
        file_match = file_path_regex.match(line)
        if file_match:
            current_file = file_match.group(2)
            files_changed.add(current_file)
            context_line = ""
            continue

        hunk_match = hunk_header_regex.match(line)
        if hunk_match:
            old_line_num = int(hunk_match.group(1))
            new_line_num = int(hunk_match.group(3))
            context_line = ""
            continue

        if not current_file or line.startswith("---") or line.startswith("+++"):
            continue

        # Track the last relevant definition line as context for sorries
        if any(keyword in line for keyword in SORRY_KEYWORDS):
            context_line = re.sub(r"^[+-]\s*", "", line)

        if line.startswith('+'):
            lines_added += 1
            if 'sorry' in line:
                raw_added.append({'file': current_file, 'context': context_line.strip(), 'line': new_line_num})
            new_line_num += 1
        elif line.startswith('-'):
            lines_removed += 1
            if 'sorry' in line:
                raw_removed.append({'file': current_file, 'context': context_line.strip(), 'line': old_line_num})
            old_line_num += 1
        else: # Unchanged line
            old_line_num += 1
            new_line_num += 1


    # Second pass: correlate added and removed sorries
    removed_contexts = {f"{s['file']}:{s['context']}": s for s in raw_removed}

    for sorry in raw_added:
        key = f"{sorry['file']}:{sorry['context']}"
        if key in removed_contexts:
            # This is an affected sorry (moved or modified)
            removed_sorry = removed_contexts.pop(key) # Remove from dict to avoid double counting
            affected_sorries.append({
                'file': sorry['file'],
                'context': sorry['context'],
                'old_line': removed_sorry['line'],
                'new_line': sorry['line']
            })
        else:
            # This is a new sorry
            added_sorries.append(f'`{sorry["context"]}` in `{sorry["file"]}`' if sorry["context"] else f'in `{sorry["file"]}`')

    # Any remaining sorries in removed_contexts are truly removed
    for key, sorry in removed_contexts.items():
        removed_sorries.append(f'`{sorry["context"]}` in `{sorry["file"]}`' if sorry["context"] else f'in `{sorry["file"]}`')


    stats = {
        "files_changed": len(files_changed),
        "lines_added": lines_added,
        "lines_removed": lines_removed,
    }
    return stats, added_sorries, removed_sorries, affected_sorries

# --- Comment Formatting ---
def format_summary(ai_summary, stats, added_sorries, removed_sorries, affected_sorries, truncated, issues):
    """Formats the final summary comment in Markdown."""
    
    summary = f"### 🤖 Gemini PR Summary\n\n{COMMENT_IDENTIFIER}\n\n"
    summary += f"{ai_summary}\n"
    if truncated:
        summary += "> *Note: The diff was too large to be fully analyzed and was truncated.*\\n"
    
    summary += "\n---\n\n"
    summary += "**Analysis of Changes**\n\n"
    summary += "| Metric | Count |\n| --- | --- |\n"
    summary += f"| 📝 **Files Changed** | {stats['files_changed']} |\n"
    summary += f"| ✅ **Lines Added** | {stats['lines_added']} |\n"
    summary += f"| ❌ **Lines Removed** | {stats['lines_removed']} |\n"

    summary += "\n---\n\n"
    summary += "**`sorry` Tracking**\n\n"
    
    if removed_sorries:
        summary += f"*   ✅ **Removed:** {len(removed_sorries)} `sorry`(s)\n"
        for sorry in removed_sorries:
            summary += f"    *   {sorry}\n"
    
    if added_sorries:
        summary += f"*   ❌ **Added:** {len(added_sorries)} `sorry`(s)\n"
        for sorry in added_sorries:
            summary += f"    *   {sorry}\n"

    if affected_sorries:
        summary += f"*   ✏️ **Affected:** {len(affected_sorries)} `sorry`(s) (line number changed)\n"
        for sorry in affected_sorries:
            # Find the corresponding issue
            issue_link = ""
            for issue in issues:
                if f"`{sorry['context']}` in `{sorry['file']}`" in issue.title:
                    issue_link = f" (closes #{issue.number})"
                    break
            summary += f"    *   `{sorry['context']}` in `{sorry['file']}` moved from L{sorry['old_line']} to L{sorry['new_line']}{issue_link}\n"


    if not added_sorries and not removed_sorries and not affected_sorries:
        summary += "*   No `sorry`s were added, removed, or affected.\n"

    timestamp = datetime.utcnow().strftime("%Y-%m-%d %H:%M UTC")
    summary += f"\n---\n\n*Last updated: {timestamp}. See the [main CI run](https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions) for build status.*"
    
    return summary


# --- GitHub Interaction ---
def post_github_comment(summary):
    """Finds and updates an existing comment or creates a new one."""
    token = os.environ["GITHUB_TOKEN"]
    repo_name = os.environ["GITHUB_REPOSITORY"]
    pr_number = int(os.environ["PR_NUMBER"])

    auth = Auth.Token(token)
    g = Github(auth=auth)
    repo = g.get_repo(repo_name)
    pr = repo.get_pull(pr_number)

    existing_comment = None
    for comment in pr.get_issue_comments():
        if COMMENT_IDENTIFIER in comment.body:
            existing_comment = comment
            break
    
    if existing_comment:
        existing_comment.edit(summary)
        print("Updated existing comment.")
    else:
        pr.create_issue_comment(summary)
        print("Created a new comment.")

# --- Main Execution ---
if __name__ == "__main__":
    if "GEMINI_API_KEY" not in os.environ:
        print("Error: GEMINI_API_KEY environment variable not set.")
        sys.exit(1)
    genai.configure(api_key=os.environ["GEMINI_API_KEY"])

    try:
        with open("pr.diff", "r") as f:
            diff = f.read()
    except FileNotFoundError:
        print("Error: pr.diff not found.")
        sys.exit(1)

    stats, added_sorries, removed_sorries, affected_sorries = analyze_diff(diff)
    ai_summary, truncated = generate_ai_summary(diff)
    
    # Fetch sorry issues
    token = os.environ.get("GITHUB_TOKEN")
    repo_name = os.environ.get("GITHUB_REPOSITORY")
    issues = []
    if token and repo_name:
        auth = Auth.Token(token)
        g = Github(auth=auth)
        repo = g.get_repo(repo_name)
        issues = find_sorry_issues(repo)

    final_summary = format_summary(ai_summary, stats, added_sorries, removed_sorries, affected_sorries, truncated, issues)
    
    if "GITHUB_TOKEN" not in os.environ:
        print("Not in GitHub Actions context. Printing summary instead of posting:")
        print(final_summary)
    else:
        post_github_comment(final_summary)
