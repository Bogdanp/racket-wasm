(module
 (type (func (param i32) (param i64) (result i32)))
 (func
  (type 0)
  (i32.const 1))
 (func
  (i32.const 1)
  (i64.const 2)
  (call 0)
  (drop)))