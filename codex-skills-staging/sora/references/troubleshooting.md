# Troubleshooting

`401` or auth failures:
- Verify `OPENAI_API_KEY` is set in the shell you are using.

Immediate validation errors:
- Check that `--seconds` is one of `4`, `8`, or `12`.
- Check that `--size` is one of the currently documented resolutions.
- If `--input-reference` is used, make sure the image resolution exactly matches `--size`.

Job fails after queueing:
- Inspect the JSON emitted by `status` or by the `create-and-poll` command.
- Look for the API error payload under `error`.
- Tighten or simplify the prompt if the failure looks like a policy or safety issue.

Download fails:
- Confirm the job status is `completed`.
- Retry promptly. The public docs note that downloadable assets are time-limited.
- If the main video download fails, try `thumbnail` or `spritesheet` to verify asset availability.

Progress appears stuck:
- Long renders can stay `queued` or `in_progress` for minutes.
- Increase the poll interval if you are checking many jobs.

Python issues:
- Install the SDK with `pip install openai`
- Confirm the environment running the script is the one where the package is installed
