(module
  (type (;0;) (func (param i32) (result i32)))
  (func (;0;) (type 0) (param i32) (result i32)
    local.get 0
    i32.const 2
    i32.gt_s
    if (result i32)  ;; label = @1
      local.get 0
      i32.const 2
      i32.sub
      call 0
      local.get 0
      i32.const 1
      i32.sub
      call 0
      i32.add
    else
      i32.const 1
    end)
  (func (;1;) (result i32)
    i32.const 8
    call 0)
  (export "main" (func 1)))
