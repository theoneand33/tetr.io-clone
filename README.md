# webtris

webtris is a browser-based Tetris game inspired by tetr.io. It is built with plain JavaScript, HTML, and canvas drawing, with no build step, framework, or package manager required.

## Features

- Classic falling-block gameplay with score, level, and line tracking
- Multiple game modes including sprint, blitz, marathon, zen, and versus AI
- Hold, next queue, ghost piece, and soft drop support
- Keyboard controls with customizable key bindings saved in localStorage
- Persistent best scores and settings in the browser
- Local wallpaper cycling from the public directory
- Web Audio API sound effects using oscillators, with no external audio files
- Single-file game logic in game.js with bot logic in bot.js

## Requirements

- A modern browser with JavaScript enabled
- No npm install, no build tools, and no dependency setup

## Run the game

1. Open the repository folder in your file browser.
2. Open index.html in a browser.
3. The game should start immediately.

If you prefer a local web server, any static file server will work, but this project is designed to run directly from the file without a build process.

## Controls

Default controls:

- Left: Left Arrow
- Right: Right Arrow
- Soft Drop: Down Arrow
- Rotate Counterclockwise: Z
- Rotate Clockwise: X
- Hard Drop: Space
- Hold: C
- Retry: R
- Pause: Escape
- Quit: Q

## Project structure

- index.html: page entry point
- game.js: core Tetris gameplay, rendering, modes, settings, and input
- bot.js: AI logic used for versus mode
- style.css: page styling
- public/: local wallpaper assets

## Persistence

The game stores settings, key bindings, and best scores in browser localStorage so preferences persist between sessions.

## Notes

This project intentionally keeps the implementation lightweight and browser-native. The code follows a no-framework, no-module approach and avoids external dependencies.
