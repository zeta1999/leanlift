// Example source (C++): derivative-free optimization (à la NLOpt's local
// no-derivative family) — HOOKE–JEEVES PATTERN SEARCH.
//
//   hooke_jeeves(x0, y0, step): minimize f(x,y) = (x-1)^2 + (y-2)^2 using only
//     function values — NO gradient. From (x0,y0) with exploratory step `step`,
//     probe ±step along each coordinate, accept any improving move; if a full
//     sweep finds no improvement, halve the step. Return the best objective.
//
// Derivative-free is the contrast with gd.cpp: the same quadratic, optimized
// with comparisons of f only. Embedded/numerical style: a bounded loop (100
// sweeps), only `+ - *` and comparisons. Compiled `-ffp-contract=off`.
//
// Mirrors examples/opt/Hj.lean op-for-op.

extern "C" double hooke_jeeves(double x0, double y0, double step) noexcept {
    double x = x0, y = y0, h = step;
    double fbest = (x - 1.0) * (x - 1.0) + (y - 2.0) * (y - 2.0);
    for (int i = 0; i < 100; ++i) {
        double nx = x, ny = y;
        // explore along x: try +h, else -h
        double fxp = (nx + h - 1.0) * (nx + h - 1.0) + (ny - 2.0) * (ny - 2.0);
        if (fxp < fbest) {
            nx = nx + h;
            fbest = fxp;
        } else {
            double fxm = (nx - h - 1.0) * (nx - h - 1.0) + (ny - 2.0) * (ny - 2.0);
            if (fxm < fbest) {
                nx = nx - h;
                fbest = fxm;
            }
        }
        // explore along y (from the possibly-updated nx): try +h, else -h
        double fyp = (nx - 1.0) * (nx - 1.0) + (ny + h - 2.0) * (ny + h - 2.0);
        if (fyp < fbest) {
            ny = ny + h;
            fbest = fyp;
        } else {
            double fym = (nx - 1.0) * (nx - 1.0) + (ny - h - 2.0) * (ny - h - 2.0);
            if (fym < fbest) {
                ny = ny - h;
                fbest = fym;
            }
        }
        if (nx == x && ny == y) {
            h = h * 0.5;  // no improvement this sweep → shrink the step
        } else {
            x = nx;       // accept the exploratory move
            y = ny;
        }
    }
    return fbest;
}
