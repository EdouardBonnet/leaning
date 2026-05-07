# Leaneage

Static browser for the Lean files in `../twin-width`.

## Render

The default `render.yaml` uses Render's native Node runtime, not Docker. Its
build command regenerates `lean-data.js` from `../twin-width`, and its start
command runs the small Node server in this directory.

This keeps deploys fast. Server-side Compile is available only in environments
where `lake` is already on `PATH`; the current Render setup intentionally does
not install Lean during deploy.

Render does not let an existing service switch runtime after creation. If the
current `leaneage` service was created as Docker, create a fresh Node service
from this blueprint, or delete and recreate the existing service.

## Use

Run the local server when you want Import and Compile to touch the Lean project:

```sh
node server.js
```

Then open <http://127.0.0.1:4173/>.

The page loads `lean-data.js`, renders the Lean folder tree, highlights source
files, and adds five-tick conformity controls to contract statements and
definitions. Select an excerpt inside a votable item to raise a mandatory-comment
issue for that exact text. Conformity tallies, local users, night mode, issue
reports, and issue replies are stored in the browser's `localStorage`. Compile
output appears in the main workspace below the source view.

Login passwords are local to the browser storage used by the viewer. Moderator
rights are not selectable in the UI; they are assigned only to prescribed user
names in `app.js`.

Opening `index.html` directly still works for browsing and local-only state, but
Compile cannot run `lake build` and Import only adds files to the in-browser
tree until the page is refreshed.

## Refresh Data

Run this from the `twin-width-viewer` directory after the Lean source changes:

```sh
node scripts/generate-data.mjs ../twin-width lean-data.js
```

The generated data contains the Lean source text and declaration index, so no
server is required.
