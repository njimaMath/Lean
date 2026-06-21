# Codex sandbox notes

When this skill is used inside Codex, two environment limits can matter:

1. Network access
- Some Codex sessions block outbound network access.
- If outbound access is blocked, the skill cannot call the OpenAI API from inside the sandbox.

2. Writable roots
- Some Codex sessions can read `~/.codex/skills` but cannot write to it.
- In that case, stage skill files inside a writable workspace directory and move them into `~/.codex/skills` outside the sandbox.

Practical fallback:
- Keep the skill bundle in a workspace path such as `codex-skills-staging/`
- Copy it into `~/.codex/skills/` from a normal shell outside the restricted session
