(module
 (type (func (result i32 i32)))
 (export "main" (func 0))
 (func
  (result i32)
  (i32.const 1)
  (block
   (result i32)
   (unreachable))
  (i32.add)))