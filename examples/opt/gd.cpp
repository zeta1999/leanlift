// Example source (C++): multi-D optimization WITH GRADIENT — gradient descent.
//
//   gd(x0, y0, eta): minimize  f(x,y) = (x-1)^2 + (y-2)^2  by fixed-step
//     gradient descent from (x0,y0). The analytic gradient is
//     ∇f = (2(x-1), 2(y-2)); each step is  p <- p - eta*∇f(p).  After a fixed
//     number of steps return the final objective value  f(x_K, y_K)  (one f64).
//
// Embedded/numerical style: a fixed step count (no convergence test → a totally
// bounded loop), only `+ - * /`. For the quadratic the iteration is stable iff
// 0 < eta < 1 (the contraction factor is |1 - 2eta|); eta = 0.5 hits the
// minimum in one step. Compiled `-ffp-contract=off`.
//
// Mirrors examples/opt/Gd.lean op-for-op.

extern "C" double gd(double x0, double y0, double eta) noexcept {
    double x = x0, y = y0;
    for (int i = 0; i < 200; ++i) {
        double gx = 2.0 * (x - 1.0);  // ∂f/∂x
        double gy = 2.0 * (y - 2.0);  // ∂f/∂y
        x = x - eta * gx;
        y = y - eta * gy;
    }
    return (x - 1.0) * (x - 1.0) + (y - 2.0) * (y - 2.0);
}
