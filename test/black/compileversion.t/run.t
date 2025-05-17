Copy the symlinks to actual files locally, so the modification-times test works

  $ cp load.ny load2.ny
  $ cp load.nyo load2.nyo

If the compiled file format has changed but __COMPILE_VERSION__ wasn't updated, this test will fail with a segfault.  After updating __COMPILE_VERSION__, it will instead fail with "can't write compiled file"; then you need to recompile test.nyo.

  $ narya -e 'import "load2"'
