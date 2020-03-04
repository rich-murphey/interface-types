# Getenv Function

The `getenv` function builds on `countCodes` by also returning a `string`. Its
interface type signature is:

```
getenv:(string)=>string
```

## Export


```
(@interface func (export "getenv")
  (param $str string) (result string)
  local.get $str
  string.size
  allocate “memx” “malloc”
    local.get $str
    string-to-memory
    call "getenv_"
    memory-to-string "memx"
  deferred
    call $release
  end
)

(memory (export "memx") 1)

(func (export "malloc")
  (param $sze i32) (result i32)
  ...
)
```

## Import

The importer must also export a version of `malloc` so that the returned string can be
stored.

```
(func $getenv_ (import ("" "getenv_"))
  (param i32 i32) (result i32 i32))

(@interface func $getenv (import "" "getenv")
  (param $str string) (result string))

(@interface implement (import "" "getenv_")
  (param $ptr i32) (param $len i32) (result i32))
  local.get $ptr
  local.get $len
  memory-to-string "memi"
  call-import $getenv
  dup
  string.size
  allocate “memi” “malloc”
    string-to-memory
  end
)

(memory (export "memi" 1)

(func (export "malloc")
  (param $sze i32) (result i32)
  ...
)
```


## Adapter

After initial inlining

```
(func $getenv_ 
  (param $ptr i32) (param $len i32) (result i32))
  local.get $ptr
  local.get $len
  memory-to-string "memi"

  let (local $str string) (result string)
    local.get $str
    string.size
    allocate “memx” “malloc”
      local.get $str
      string-to-memory
      call "x:getenv_"
      memory-to-string "memx"
    deferred
      call $release
    end
  end
  
  dup
  string.size
  allocate “memi” “malloc”
    string-to-memory
  end
)
```

After merging string-to-memory and memory-to-string

```
(@func $getenv_
  (param $ptr i32) (param $len i32) (result i32))
  local.get $len
  allocate “memx” “malloc”
    let (local $str i32)
      local.get $ptr
      local.get $str
      local.get $len
      memcopy "memi" "memx"

      call "x:getenv_"
      let (local $res i32) (local $reslen is32)
        local.get $reslen
        allocate “memi” “malloc”
        let (local $tgt i32)
          local.get $res
          local.get $tgt
          local.get $reslen
          memcopy "memx" "memi"
        end
      end
    deferred
      call $release
    end
  end
)
```
