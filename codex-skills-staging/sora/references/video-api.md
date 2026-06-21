# Current video API notes

These notes are aligned to the public OpenAI video documentation available on March 16, 2026.

Core create endpoint:
- `client.videos.create(...)`
- Models: `sora-2`, `sora-2-pro`
- Durations: `4`, `8`, `12` seconds
- Sizes: `720x1280`, `1280x720`, `1024x1792`, `1792x1024`

Polling and retrieval:
- `client.videos.retrieve(video_id)`
- Typical states: `queued`, `in_progress`, `completed`, `failed`
- Poll at a reasonable interval such as 10 to 20 seconds

Download:
- `client.videos.download_content(video_id, variant="video")`
- Supported asset variants in the public guide:
  - `video`
  - `thumbnail`
  - `spritesheet`
- Download URLs and downloadable assets are short-lived. The guide notes that video download URLs are valid for up to 1 hour after generation.

Image references:
- The public guide says `input_reference` can be used with a local uploaded image in multipart requests.
- Supported formats: JPEG, PNG, WebP
- The reference image must match the requested output `size`

Batch:
- Batch currently supports `POST /v1/videos` only
- Batch requests use JSON, not multipart
- For Batch image-guided jobs, `input_reference` must be an object containing either `file_id` or `image_url`

Useful Python methods shown in the public docs:
- `client.videos.create(...)`
- `client.videos.remix(video_id=..., prompt=...)`
- `client.videos.retrieve(video_id)`
- `client.videos.list(...)`
- `client.videos.delete(video_id)`
- `client.videos.download_content(video_id, variant="video")`
