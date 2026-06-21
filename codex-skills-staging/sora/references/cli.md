# CLI usage

This staged fallback ships a small Python CLI at `scripts/sora.py`.

Prerequisites:
- `OPENAI_API_KEY` must be set.
- `openai` must be installed in the Python environment you plan to use.
- For image-guided generations, the input image size must exactly match the requested `--size`.

Common commands:

Create a render and wait for completion:

```bash
python scripts/sora.py create-and-poll \
  --prompt "A handheld tracking shot through a rainy Tokyo alley at night" \
  --model sora-2-pro \
  --seconds 8 \
  --size 1280x720 \
  --output alley.mp4
```

Create an image-guided render:

```bash
python scripts/sora.py create \
  --prompt "The mascot turns, waves, and walks out of frame" \
  --model sora-2-pro \
  --seconds 8 \
  --size 1280x720 \
  --input-reference first-frame.png
```

Remix a completed video:

```bash
python scripts/sora.py remix-and-poll \
  --video-id video_123 \
  --prompt "Keep the same composition, but switch the lighting to sunrise gold"
```

Inspect status:

```bash
python scripts/sora.py status --video-id video_123
```

Download assets from a completed render:

```bash
python scripts/sora.py download --video-id video_123 --variant video --output render.mp4
python scripts/sora.py download --video-id video_123 --variant thumbnail --output render.webp
python scripts/sora.py download --video-id video_123 --variant spritesheet --output render.jpg
```

List recent jobs:

```bash
python scripts/sora.py list --limit 10 --order desc
```
