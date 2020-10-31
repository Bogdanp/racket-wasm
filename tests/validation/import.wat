(module
 (import "foo" "id" (func $id1 (param i32) (result i32)))
 (import "foo" "id" (func $id2 (param i32) (result i32)))
 (import "foo" "id" (func $id3 (param i32) (result i32)))
 (func
   (result i32)
   (i32.const 1)
   (call $id3)))