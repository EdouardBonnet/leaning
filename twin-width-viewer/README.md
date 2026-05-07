# Leaneage

Static browser for the Lean files in `../twin-width`.

## Render

The default root `Dockerfile` is optimized for fast Render deploys. It uses a
Node-only image, regenerates `lean-data.js`, and serves the viewer. Server-side
Compile is disabled in that fast image because installing Lean/mathlib makes
Render builds much slower.

Use `Dockerfile.lean` instead only if the deployed service must run `lake build`
from the Compile button.

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
