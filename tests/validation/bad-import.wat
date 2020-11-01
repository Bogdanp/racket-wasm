(module
 (type (func))
 (type (func (param i32) (result i32)))
 (import "a" "m" (memory 0))
 (import "a" "f" (func $f (type 1)))
 (func
  (call $f)))