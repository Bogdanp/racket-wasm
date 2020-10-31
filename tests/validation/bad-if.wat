(module
 (export "main" (func $main))
 (func $main
   (result i32)
   (i32.const 1)
   (if
    (then
     (i32.const 42)
     (drop)))))
