# dependent-map

This is a port of the [`dependent-map`](https://hackage.haskell.org/package/dependent-map) package from Haskell

## Notes
- I originally implemented it as part of my project, so some things that were not needed there are missing.
- In the original code there was some pointer equality magic, that I did not understand, that I had to rewrite in a conventional way, possibly to the detriment perfomance.
- For now, the package contains some elements of the [`dependent-sum`](https://hackage.haskell.org/package/dependent-sum) and [`some`](https://hackage.haskell.org/package/some) packages as I needed them too.
