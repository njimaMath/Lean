# Prompting guidance

Treat video prompts as shot briefs, not single-sentence labels.

Include:
- subject
- action
- location
- camera behavior
- lighting
- tone or style

Good structure:
1. Subject and action
2. Environment and time of day
3. Camera move or framing
4. Look and mood
5. Constraints that must stay fixed

Example:

```text
A calm red fox barista prepares tea in a tiny wooden cafe at dawn. Slow dolly-in from medium shot to close-up. Warm backlight through fogged windows, floating dust, shallow depth of field, gentle steam, understated cinematic realism.
```

For remixes:
- Name the one or two changes you want.
- State what must remain unchanged.
- Avoid rewriting the whole concept unless you want a larger drift.

Example remix prompt:

```text
Keep the same composition and action, but change the lighting to cool blue hour and add rain reflections on the pavement.
```

When using an input image:
- Describe motion after the opening frame.
- Mention continuity goals explicitly.
- Avoid contradictory camera instructions.
