# Campaign lessons

- Performance reports must set and record `RAYON_NUM_THREADS` explicitly. A default Rayon run is
  multithreaded even when the product's `parallel` feature is not named directly, because dependency
  feature unification can enable Stwo's parallel paths. Every benchmark result line must expose the
  effective Rayon thread count before it is compared with a one-thread campaign baseline.
