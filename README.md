# A product inequality for positive semidefinite matrices

Saigyukari

For a complex positive semidefinite matrix $A=(a_{ij})$ of order $n$,
the main theorem proves

$$
\prod_{i,j=1}^n |1-a_{ij}| \le \prod_{i=1}^n |1-a_{ii}^{\,n}|.
$$

The paper proves the inequality analytically, with a log-concave density
comparison and a scalar differential equation supplying the fourth-order
differential estimate. Lean 4 checks the full proof, including the estimate
and its quantitative lower bound. [Paper](paper/psd_product.pdf) ·
[Companion remarks](paper/psd_product_remarks.pdf)

## Reproduce the Lean build

Install Elan and Git, then run these commands from the repository root in
a POSIX shell. The first run needs network access for the pinned toolchain,
the locked dependencies, and the Mathlib cache. [Elan](https://github.com/leanprover/elan)

```sh
lake exe cache get $(sed -n 's/^import //p' PsdProduct.lean)
lake build --wfail
```

The cache step is optional. `lake build --wfail` can build the locked
dependencies from source.

`lean-toolchain` selects Lean `v4.36.0`. `lakefile.toml` pins Mathlib to
`v4.36.0`, and `lake-manifest.json` records the exact commits, including
the transitive dependencies. The Mathlib commit is
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The checked-in manifest suffices
for normal builds.

The build prints the dependency report from
`#print axioms psd_product_inequality`.

```text
'psd_product_inequality' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Rebuild the PDFs

Use a LaTeX installation with `latexmk`, AMS-LaTeX, Latin Modern, and
`geometry`.

```sh
cd paper
latexmk -pdf -outdir=build psd_product.tex psd_product_remarks.tex
```

## Publish on GitHub

Create an empty GitHub repository. From the extracted source directory,
initialize Git and push to that repository.

```sh
git init -b main
git add .
git commit -m 'Publish the computer-free proof'
git remote add origin https://github.com/YOUR-ACCOUNT/psd-product-inequality.git
git push -u origin main
```

GitHub Actions builds the Lean target and checks its axiom report on pushes
and pull requests.

Distributed under the [MIT License](LICENSE).
