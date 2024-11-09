# dependent-map

This is a port of the
[`dependent-map`](https://hackage.haskell.org/package/dependent-map)
package from Haskell

## Notes
- I originally implemented it as part of my project, so some things that were
  not needed there are missing.
- In the original code there was some pointer equality magic, that I did not
  understand, that I had to rewrite in a conventional way, possibly to the
  detriment of perfomance.
- For now, the package contains some elements of the
  [`dependent-sum`](https://hackage.haskell.org/package/dependent-sum) and
  [`some`](https://hackage.haskell.org/package/some) packages as I needed them
  too.

## License
As mentioned above, the is derived from three sources:
[`dependent-map`](https://hackage.haskell.org/package/dependent-map),
[`dependent-sum`](https://hackage.haskell.org/package/dependent-sum) and
[`some`](https://hackage.haskell.org/package/some).

The license in
[`dependent-map`](https://hackage.haskell.org/package/dependent-map) mentions
that it was derived from the
[`containers`](https://hackage.haskell.org/package/containers) package which
was allegedly based on the GHC project and two papers. However, the references
to the two papers were removed in the
[`containers`](https://hackage.haskell.org/package/containers) package
(https://github.com/haskell/containers/commit/14eb7c2665382d54bfdf37f3687e2cd431f7c7b9)
and it only mentions the GHC project now. I therefore omit these two copyright
notices in the license of this project.

The authors of
[`dependent-map`](https://hackage.haskell.org/package/dependent-map) and
[`dependent-sum`](https://hackage.haskell.org/package/dependent-sum) state
that they consider their contributions public domain.

The licenses of the original projects can be found in the `original-licenses`
folder
