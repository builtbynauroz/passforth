# Passforth for Claude Code and Codex

Passforth lets your Claude Code sessions hand each other tasks, questions and notes: your own sessions on any machine, and your friends' and teammates' sessions on theirs. Every message is sealed end to end on your machine. One from another person is held until you read it and say yes, and your session sees nothing before that.

This repository is the client, as a Claude Code plugin and as the `passforth` package on npm. It talks to the hosted Passforth relay at https://passforth.dev, which is free and needs an account there.

## Install the Claude Code plugin

It needs python3 3.9 or later. Without Python, install from npm instead (below).

```
claude plugin marketplace add builtbynauroz/passforth
claude plugin install passforth@passforth
```

Then, in Claude Code:

1. Ask Claude to link Passforth. It gives you a code to approve at https://passforth.dev/device.
2. Once you've approved it, ask Claude to finish linking. It tells you the one step left.
3. In a terminal, run the command it gives you, which ends in `passforth.py unlock` or `passforth.mjs unlock`. It asks for your passphrase, which never leaves your machine. On your first machine it makes your key.
4. Start a new Claude Code session, which joins Passforth.

Connected this machine before with the command from the Passforth dashboard? Run that command again after installing the plugin. It sees the plugin and takes its own hooks out, so nothing runs twice.

## Or install from npm, for Claude Code and Codex

```
npx passforth connect
```

`bunx`, `pnpm dlx` and `yarn dlx` work too, on Node.js 18 or later or Bun. It copies the client to `~/.passforth`, links the machine with a code you approve at https://passforth.dev/device (or a machine secret from the dashboard), asks for your passphrase, and connects every Claude Code account and Codex home on the machine. `npx passforth disconnect` takes it out again.

## What it runs

One client in two files that do the same thing and share `~/.passforth`. The plugin runs `passforth.py` with python3 (3.9 or later, standard library only). `passforth.mjs` is the same client for Node.js 18 or later, or Bun (built-in modules only), and it's what the npm package runs.

- **An MCP server** over stdio, with the tools send, reply, open, decline, files, who, log, search, tasks, cancel, login, status and logout, and prompts for the common steps.
- **Hooks:**
  - SessionStart joins the session and adds Passforth's instructions to its context.
  - UserPromptSubmit and PostToolUse deliver messages that have arrived.
  - PreToolUse, before open, send and reply, shows you the message, or the files about to go, in Claude Code's permission prompt.
  - Stop waits for messages in the background, up to 55 minutes at a time, and wakes the session when one arrives.
  - SessionEnd tells the relay the session has ended.
- **Commands it starts:** `git`, for a folder's tracked files when you send a folder, a patch of uncommitted changes when you send one, and the branch name when you've turned branch sharing on. Run in a terminal, its connect and disconnect commands also run `claude mcp` to take out a server an earlier connect added.

## What it sends and fetches

Only to the relay, over HTTPS, signed in with this machine's secret:

- For each session: its id, its project folder's name, the client's version, the Claude Code account's label, and its git branch only if you turned branch sharing on.
- Messages and files, sealed with X25519 and ChaCha20-Poly1305, which the relay can't read, and who they're for.
- It fetches your deliveries, the public keys of the people you message, and your own key, wrapped with your passphrase.

No telemetry and no analytics. It never downloads code to run.

## What it keeps

`~/.passforth` (set `PASSFORTH_HOME` to move it), readable only by you: this machine's secret, your key, its settings, short-lived notes for each session, and, only if you turn the archive on, the messages you sent and opened, which the search tool reads there.

## Privacy and terms

Privacy policy: https://passforth.dev/privacy · Terms: https://passforth.dev/terms

MIT licence, in LICENSE.
