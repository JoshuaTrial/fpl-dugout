# FPL Dugout

A live Fantasy Premier League dashboard. One Python file, standard library only.

## Run locally

    python3 fpl_dugout.py

Opens http://localhost:8756.

## Deploy on Render

1. Push this folder to a GitHub repository.
2. In Render: **New → Blueprint**, point it at the repo. It reads `render.yaml`.
3. Set `FPL_PASSWORD` in the dashboard to something only your league knows.
4. Deploy. The URL is `https://<name>.onrender.com`.

Without `render.yaml`, create a **Web Service** manually with:

| Setting | Value |
|---|---|
| Runtime | Python 3 |
| Build command | `python -m compileall fpl_dugout.py` |
| Start command | `python fpl_dugout.py` |
| Health check path | `/healthz` |

## Environment variables

| Variable | Meaning |
|---|---|
| `PORT` | Set by Render. Its presence makes the app bind `0.0.0.0` instead of loopback. |
| `FPL_ENTRY` | Default FPL team id. |
| `FPL_LEAGUE` | Classic league id. |
| `FPL_PASSWORD` | If set, the site asks for a password. Any username, this password. |
| `HOST` | Override the bind address. Rarely needed. |

## Notes

- All data is public FPL API data, read-only. The app cannot change your team.
- The free plan sleeps after ~15 minutes idle; the next visit takes ~30-60s to wake.
- Responses are cached for 90 seconds so the FPL API is not hammered.
