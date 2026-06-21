#!/usr/bin/env python3
"""Small CLI for OpenAI video generation jobs."""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Any

from openai import OpenAI


VIDEO_VARIANTS = {
    "video": ".mp4",
    "thumbnail": ".webp",
    "spritesheet": ".jpg",
}


def _as_dict(value: Any) -> Any:
    if hasattr(value, "model_dump"):
        return value.model_dump()
    if hasattr(value, "to_dict"):
        return value.to_dict()
    if isinstance(value, dict):
        return value
    return value


def _print_json(value: Any) -> None:
    print(json.dumps(_as_dict(value), indent=2, sort_keys=True, default=str))


def _error_message(video: Any) -> str:
    error = getattr(video, "error", None)
    if error is None:
        return "Video generation failed."
    if isinstance(error, dict):
        return str(error.get("message") or error)
    message = getattr(error, "message", None)
    return str(message or error)


def _default_output(video_id: str, variant: str) -> Path:
    suffix = VIDEO_VARIANTS[variant]
    return Path(f"{video_id}{suffix}")


def _write_download(client: OpenAI, video_id: str, variant: str, output: Path) -> Path:
    output.parent.mkdir(parents=True, exist_ok=True)
    content = client.videos.download_content(video_id, variant=variant)
    if hasattr(content, "write_to_file"):
        content.write_to_file(str(output))
    else:
        output.write_bytes(content.read())
    return output


def _render_progress(video: Any) -> None:
    progress = float(getattr(video, "progress", 0) or 0)
    status = getattr(video, "status", "unknown")
    width = 30
    filled = int((progress / 100.0) * width)
    bar = "=" * filled + "-" * (width - filled)
    status_text = "Queued" if status == "queued" else "Processing"
    sys.stdout.write(f"\r{status_text}: [{bar}] {progress:5.1f}%")
    sys.stdout.flush()


def _poll_video(client: OpenAI, video_id: str, interval: int) -> Any:
    while True:
        video = client.videos.retrieve(video_id)
        status = getattr(video, "status", None)
        if status in {"queued", "in_progress"}:
            _render_progress(video)
            time.sleep(interval)
            continue
        if status is not None:
            sys.stdout.write("\n")
        return video


def _generation_kwargs(args: argparse.Namespace) -> tuple[dict[str, Any], list[Any]]:
    kwargs: dict[str, Any] = {
        "prompt": args.prompt,
        "model": args.model,
    }
    handles: list[Any] = []
    if args.seconds is not None:
        kwargs["seconds"] = str(args.seconds)
    if args.size is not None:
        kwargs["size"] = args.size
    if getattr(args, "input_reference", None):
        path = Path(args.input_reference)
        handle = path.open("rb")
        handles.append(handle)
        kwargs["input_reference"] = handle
    return kwargs, handles


def _close_all(handles: list[Any]) -> None:
    for handle in handles:
        handle.close()


def cmd_create(args: argparse.Namespace) -> int:
    client = OpenAI()
    kwargs, handles = _generation_kwargs(args)
    try:
        video = client.videos.create(**kwargs)
    finally:
        _close_all(handles)
    _print_json(video)
    return 0


def cmd_create_and_poll(args: argparse.Namespace) -> int:
    client = OpenAI()
    kwargs, handles = _generation_kwargs(args)
    try:
        video = client.videos.create(**kwargs)
    finally:
        _close_all(handles)
    print(f"Started video job {video.id}")
    video = _poll_video(client, video.id, args.poll_interval)
    if getattr(video, "status", None) != "completed":
        print(_error_message(video), file=sys.stderr)
        _print_json(video)
        return 1
    output = Path(args.output) if args.output else _default_output(video.id, "video")
    _write_download(client, video.id, "video", output)
    print(f"Saved video to {output}")
    _print_json(video)
    return 0


def cmd_remix(args: argparse.Namespace) -> int:
    client = OpenAI()
    video = client.videos.remix(
        video_id=args.video_id,
        prompt=args.prompt,
    )
    _print_json(video)
    return 0


def cmd_remix_and_poll(args: argparse.Namespace) -> int:
    client = OpenAI()
    video = client.videos.remix(
        video_id=args.video_id,
        prompt=args.prompt,
    )
    print(f"Started remix job {video.id}")
    video = _poll_video(client, video.id, args.poll_interval)
    if getattr(video, "status", None) != "completed":
        print(_error_message(video), file=sys.stderr)
        _print_json(video)
        return 1
    output = Path(args.output) if args.output else _default_output(video.id, "video")
    _write_download(client, video.id, "video", output)
    print(f"Saved video to {output}")
    _print_json(video)
    return 0


def cmd_status(args: argparse.Namespace) -> int:
    client = OpenAI()
    video = client.videos.retrieve(args.video_id)
    _print_json(video)
    return 0


def cmd_download(args: argparse.Namespace) -> int:
    client = OpenAI()
    output = Path(args.output) if args.output else _default_output(args.video_id, args.variant)
    _write_download(client, args.video_id, args.variant, output)
    print(f"Saved {args.variant} to {output}")
    return 0


def cmd_list(args: argparse.Namespace) -> int:
    client = OpenAI()
    page = client.videos.list(
        limit=args.limit,
        order=args.order,
        after=args.after,
    )
    _print_json(page)
    return 0


def add_generation_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--prompt", required=True, help="Video prompt text.")
    parser.add_argument(
        "--model",
        default="sora-2",
        choices=["sora-2", "sora-2-pro"],
        help="Video model to use.",
    )
    parser.add_argument(
        "--seconds",
        type=int,
        choices=[4, 8, 12],
        help="Clip duration in seconds.",
    )
    parser.add_argument(
        "--size",
        choices=["720x1280", "1280x720", "1024x1792", "1792x1024"],
        help="Output resolution.",
    )
    parser.add_argument(
        "--input-reference",
        help="Optional image path for the opening frame. The image must match --size.",
    )


def add_poll_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--poll-interval",
        type=int,
        default=10,
        help="Polling interval in seconds.",
    )
    parser.add_argument(
        "--output",
        help="Output path for the downloaded MP4. Defaults to <video_id>.mp4.",
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="OpenAI Sora helper CLI.")
    subparsers = parser.add_subparsers(dest="command", required=True)

    create = subparsers.add_parser("create", help="Create a video job and return metadata.")
    add_generation_args(create)
    create.set_defaults(func=cmd_create)

    create_poll = subparsers.add_parser(
        "create-and-poll",
        help="Create a video job, poll to completion, and download the MP4.",
    )
    add_generation_args(create_poll)
    add_poll_args(create_poll)
    create_poll.set_defaults(func=cmd_create_and_poll)

    remix = subparsers.add_parser("remix", help="Create a remix job and return metadata.")
    remix.add_argument("--video-id", required=True, help="Completed source video id.")
    remix.add_argument("--prompt", required=True, help="Revised prompt for the remix.")
    remix.set_defaults(func=cmd_remix)

    remix_poll = subparsers.add_parser(
        "remix-and-poll",
        help="Create a remix job, poll to completion, and download the MP4.",
    )
    remix_poll.add_argument("--video-id", required=True, help="Completed source video id.")
    remix_poll.add_argument("--prompt", required=True, help="Revised prompt for the remix.")
    add_poll_args(remix_poll)
    remix_poll.set_defaults(func=cmd_remix_and_poll)

    status = subparsers.add_parser("status", help="Fetch video job metadata.")
    status.add_argument("--video-id", required=True, help="Video id to fetch.")
    status.set_defaults(func=cmd_status)

    download = subparsers.add_parser("download", help="Download a completed video asset.")
    download.add_argument("--video-id", required=True, help="Completed video id.")
    download.add_argument(
        "--variant",
        default="video",
        choices=sorted(VIDEO_VARIANTS),
        help="Asset variant to download.",
    )
    download.add_argument(
        "--output",
        help="Output path. Defaults to <video_id> with a variant-specific extension.",
    )
    download.set_defaults(func=cmd_download)

    list_parser = subparsers.add_parser("list", help="List recent video jobs.")
    list_parser.add_argument("--limit", type=int, default=20, help="Page size.")
    list_parser.add_argument(
        "--order",
        choices=["asc", "desc"],
        default="desc",
        help="Sort order by creation time.",
    )
    list_parser.add_argument("--after", help="Pagination cursor.")
    list_parser.set_defaults(func=cmd_list)

    return parser


def main(argv: list[str]) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
