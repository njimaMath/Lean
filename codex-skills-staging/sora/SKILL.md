# Video generation with Sora

Use the OpenAI Python SDK with the current video API to create, remix, inspect, and download videos.

Do not call the API with raw HTTP. Use the OpenAI Python SDK only.

Before any API call:
- Resolve ambiguity about the prompt, aspect ratio, duration, and whether the user wants a new render or a remix.
- If the user supplies an input image, confirm it matches the requested output size. The current public API requires the reference image resolution to match `size`.
- Keep requests inside the current public API limits described in `references/video-api.md`.
- If the user wants batch rendering, explain that Batch currently supports only `POST /v1/videos` with JSON requests, and image references must use `file_id` or `image_url`.

Workflow:
1. Choose one path:
   - New generation from a text prompt
   - Generation from one input image plus a text prompt
   - Remix of an existing completed video
2. Pick parameters grounded in the current API:
   - model: `sora-2` or `sora-2-pro`
   - seconds: `4`, `8`, or `12`
   - size: `720x1280`, `1280x720`, `1024x1792`, or `1792x1024`
3. Use the bundled CLI script to submit the job and poll until a terminal state.
4. When generation succeeds, save the video locally and report:
   - output path
   - final parameters used
   - any API error or policy notes surfaced during the run
5. If the request is under-specified, ask only the minimum follow-up questions needed to produce a useful result.

Use this script:
- `python scripts/sora.py create-and-poll --prompt "..." --model sora-2 --seconds 8 --size 1280x720`
- `python scripts/sora.py create --prompt "..." --input-reference frame.png --size 1280x720`
- `python scripts/sora.py remix-and-poll --video-id video_123 --prompt "..."`
- `python scripts/sora.py status --video-id video_123`
- `python scripts/sora.py download --video-id video_123 --output output.mp4`

Reference map:
- For exact command usage, read `references/cli.md`
- For current API behavior and limits, read `references/video-api.md`
- For prompt writing patterns, read `references/prompting.md`
- For common failures and fixes, read `references/troubleshooting.md`
- For Codex sandbox and staging constraints, read `references/codex-network.md`

Safety:
- Follow the current OpenAI policy and refuse disallowed content.
- If user-provided reference media looks risky or ambiguous, stop and clarify before sending it to the API.
