#!/usr/bin/env python3
"""
Check the status of GitHub Actions for the most recent commit or a specific PR.

This script queries the GitHub API to fetch and display the status of workflow runs
for a given commit, branch, or pull request.

Usage:
    # Check status for the most recent commit on current branch
    python scripts/check_github_actions.py

    # Check status for a specific commit
    python scripts/check_github_actions.py --commit <sha>

    # Check status for a specific PR
    python scripts/check_github_actions.py --pr <number>

    # Check status for a specific branch
    python scripts/check_github_actions.py --branch <name>

Environment Variables:
    GITHUB_TOKEN: GitHub personal access token (optional for public repos)
"""

import argparse
import json
import os
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime
from typing import Optional
from urllib import request
from urllib.error import HTTPError, URLError


@dataclass
class WorkflowRun:
    """Represents a GitHub Actions workflow run."""

    id: int
    name: str
    status: str
    conclusion: Optional[str]
    html_url: str
    created_at: str
    updated_at: str
    head_sha: str
    head_branch: str

    @property
    def display_status(self) -> str:
        """Get a human-readable status with emoji."""
        if self.conclusion:
            return {
                "success": "✅ Success",
                "failure": "❌ Failure",
                "cancelled": "🚫 Cancelled",
                "skipped": "⏭️  Skipped",
                "timed_out": "⏱️  Timed Out",
                "action_required": "⚠️  Action Required",
            }.get(self.conclusion, f"❓ {self.conclusion}")
        return {
            "queued": "🔵 Queued",
            "in_progress": "🔄 In Progress",
            "completed": "✓ Completed",
        }.get(self.status, f"❓ {self.status}")

    def __str__(self) -> str:
        """Format workflow run for display."""
        return (
            f"  {self.display_status}\n"
            f"  Name: {self.name}\n"
            f"  Branch: {self.head_branch}\n"
            f"  Commit: {self.head_sha[:7]}\n"
            f"  Updated: {self.format_time(self.updated_at)}\n"
            f"  URL: {self.html_url}"
        )

    @staticmethod
    def format_time(iso_time: str) -> str:
        """Format ISO timestamp to human-readable format."""
        try:
            dt = datetime.fromisoformat(iso_time.replace("Z", "+00:00"))
            return dt.strftime("%Y-%m-%d %H:%M:%S UTC")
        except Exception:
            return iso_time


class GitHubAPI:
    """Simple GitHub API client."""

    BASE_URL = "https://api.github.com"

    def __init__(self, repo_owner: str, repo_name: str, token: Optional[str] = None):
        self.repo_owner = repo_owner
        self.repo_name = repo_name
        self.token = token or os.environ.get("GITHUB_TOKEN")

    def _make_request(self, endpoint: str) -> dict:
        """Make a GET request to the GitHub API."""
        url = f"{self.BASE_URL}/repos/{self.repo_owner}/{self.repo_name}/{endpoint}"
        headers = {"Accept": "application/vnd.github.v3+json"}

        if self.token:
            headers["Authorization"] = f"token {self.token}"

        req = request.Request(url, headers=headers)

        try:
            with request.urlopen(req) as response:
                return json.loads(response.read())
        except HTTPError as e:
            if e.code == 401:
                print(
                    "❌ Authentication failed. Set GITHUB_TOKEN environment variable.",
                    file=sys.stderr,
                )
            elif e.code == 404:
                print(f"❌ Resource not found: {url}", file=sys.stderr)
            else:
                print(f"❌ HTTP Error {e.code}: {e.reason}", file=sys.stderr)
            sys.exit(1)
        except URLError as e:
            print(f"❌ Network error: {e.reason}", file=sys.stderr)
            sys.exit(1)

    def get_workflow_runs(
        self, branch: Optional[str] = None, sha: Optional[str] = None
    ) -> list[WorkflowRun]:
        """Get workflow runs for a branch or commit SHA."""
        endpoint = "actions/runs"
        params = []

        if branch:
            params.append(f"branch={branch}")
        if sha:
            params.append(f"head_sha={sha}")

        if params:
            endpoint += "?" + "&".join(params)

        data = self._make_request(endpoint)
        runs = []

        for run in data.get("workflow_runs", []):
            runs.append(
                WorkflowRun(
                    id=run["id"],
                    name=run["name"],
                    status=run["status"],
                    conclusion=run.get("conclusion"),
                    html_url=run["html_url"],
                    created_at=run["created_at"],
                    updated_at=run["updated_at"],
                    head_sha=run["head_sha"],
                    head_branch=run["head_branch"],
                )
            )

        return runs

    def get_pr_info(self, pr_number: int) -> dict:
        """Get information about a pull request."""
        return self._make_request(f"pulls/{pr_number}")

    def get_commit_info(self, sha: str) -> dict:
        """Get information about a commit."""
        return self._make_request(f"commits/{sha}")


def get_git_info() -> dict:
    """Get git repository information."""

    def run_git(cmd: list[str]) -> str:
        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                check=True,
            )
            return result.stdout.strip()
        except subprocess.CalledProcessError as e:
            print(f"❌ Git command failed: {' '.join(cmd)}", file=sys.stderr)
            print(f"   {e.stderr}", file=sys.stderr)
            sys.exit(1)

    # Get remote URL
    remote_url = run_git(["git", "remote", "get-url", "origin"])

    # Parse owner and repo from URL
    # Handles: https://github.com/owner/repo.git, git@github.com:owner/repo.git
    # Also handles local proxy URLs like http://local_proxy@127.0.0.1:25831/git/owner/repo

    # Extract owner/repo from various URL formats
    if remote_url.startswith("git@github.com"):
        # git@github.com:owner/repo.git
        parts = remote_url.split(":")[-1].replace(".git", "").split("/")
    elif "github.com/" in remote_url:
        # https://github.com/owner/repo.git or http://...
        parts = remote_url.split("github.com/")[-1].replace(".git", "").split("/")
    elif "/git/" in remote_url:
        # Handle local proxy URLs like http://local_proxy@127.0.0.1:25831/git/owner/repo
        parts = remote_url.split("/git/")[-1].replace(".git", "").split("/")
    else:
        print(f"❌ Could not parse repository URL: {remote_url}", file=sys.stderr)
        print(f"   Supported formats:", file=sys.stderr)
        print(f"   - https://github.com/owner/repo.git", file=sys.stderr)
        print(f"   - git@github.com:owner/repo.git", file=sys.stderr)
        print(f"   - http://proxy/git/owner/repo", file=sys.stderr)
        sys.exit(1)

    if len(parts) < 2:
        print(f"❌ Could not parse repository owner/name from: {remote_url}", file=sys.stderr)
        sys.exit(1)

    owner = parts[0]
    repo = parts[1]

    # Get current branch
    branch = run_git(["git", "rev-parse", "--abbrev-ref", "HEAD"])

    # Get current commit SHA
    sha = run_git(["git", "rev-parse", "HEAD"])

    return {
        "owner": owner,
        "repo": repo,
        "branch": branch,
        "sha": sha,
        "remote_url": remote_url,
    }


def main():
    parser = argparse.ArgumentParser(
        description="Check GitHub Actions status for commits, branches, or PRs",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )

    parser.add_argument(
        "--commit",
        help="Check status for a specific commit SHA",
    )
    parser.add_argument(
        "--branch",
        help="Check status for a specific branch",
    )
    parser.add_argument(
        "--pr",
        type=int,
        help="Check status for a specific pull request number",
    )
    parser.add_argument(
        "--token",
        help="GitHub personal access token (or set GITHUB_TOKEN env var)",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=5,
        help="Maximum number of workflow runs to display (default: 5)",
    )

    args = parser.parse_args()

    # Get git repository info
    git_info = get_git_info()
    print(f"📦 Repository: {git_info['owner']}/{git_info['repo']}")
    print()

    # Initialize GitHub API client
    api = GitHubAPI(git_info["owner"], git_info["repo"], args.token)

    # Determine what to check
    if args.pr:
        print(f"🔍 Checking PR #{args.pr}...")
        pr_info = api.get_pr_info(args.pr)
        sha = pr_info["head"]["sha"]
        branch = pr_info["head"]["ref"]
        print(f"   Branch: {branch}")
        print(f"   Commit: {sha[:7]}")
        print()
    elif args.commit:
        print(f"🔍 Checking commit {args.commit[:7]}...")
        sha = args.commit
        branch = None
        print()
    elif args.branch:
        print(f"🔍 Checking branch '{args.branch}'...")
        sha = None
        branch = args.branch
        print()
    else:
        # Use current branch and commit
        sha = git_info["sha"]
        branch = git_info["branch"]
        print(f"🔍 Checking current commit on branch '{branch}'...")
        print(f"   Commit: {sha[:7]}")
        print()

    # Fetch workflow runs
    runs = api.get_workflow_runs(branch=branch, sha=sha)

    if not runs:
        print("ℹ️  No workflow runs found.")
        return

    # Display results
    print(f"📊 Found {len(runs)} workflow run(s):\n")

    for i, run in enumerate(runs[: args.limit], 1):
        print(f"{i}. {run}")
        if i < min(len(runs), args.limit):
            print()

    if len(runs) > args.limit:
        print(f"\n... and {len(runs) - args.limit} more (use --limit to show more)")

    # Summary
    print("\n" + "=" * 60)
    print("📈 Summary:")

    # Count by conclusion
    conclusions = {}
    for run in runs:
        if run.conclusion:
            conclusions[run.conclusion] = conclusions.get(run.conclusion, 0) + 1

    for conclusion, count in sorted(conclusions.items()):
        emoji = {
            "success": "✅",
            "failure": "❌",
            "cancelled": "🚫",
            "skipped": "⏭️",
        }.get(conclusion, "❓")
        print(f"  {emoji} {conclusion}: {count}")

    # Overall status
    if runs and runs[0].conclusion == "success":
        print("\n✅ Most recent workflow: SUCCESS")
        return 0
    elif runs and runs[0].conclusion == "failure":
        print("\n❌ Most recent workflow: FAILED")
        return 1
    elif runs and runs[0].status == "in_progress":
        print("\n🔄 Most recent workflow: IN PROGRESS")
        return 0
    else:
        print(f"\n❓ Most recent workflow: {runs[0].display_status if runs else 'UNKNOWN'}")
        return 0


if __name__ == "__main__":
    sys.exit(main())
