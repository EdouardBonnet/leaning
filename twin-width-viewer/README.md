# Leaneage

Static browser for the Lean files in `../twin-width`.

## Render

The default root `Dockerfile` uses the Lean toolchain image and installs Node so
the deployed Compile button can run `lake build`. It also fetches the mathlib
cache during image build, so this is slower than a static viewer deployment but
keeps server-side compilation available.

Use `Dockerfile.fast` only if you want a much faster Node-only deployment and
can accept Compile being unavailable on the deployed service.

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
