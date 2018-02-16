open Core
open Async
open MacKeyFun



let command =
  Command.async
    ~summary:"generates a symmetric key"
    Command.Spec.(
      empty

      +> flag "-sym" (optional_with_default "symmetric_key1-1" string)
        ~doc:" File to read private key from (default symmetric_key1-1)"

      +> flag "-symsrc" (optional_with_default 1 int)
        ~doc:" source of symmetric key (default 1)"

      +> flag "-symdst" (optional_with_default 1 int)
        ~doc:" destination of symmetric key (default 1)"

      +> flag "-read" (optional_with_default false bool)
        ~doc:" Reading? (default false)"

      +> flag "-sign" (optional_with_default false bool)
        ~doc:" Sign? (default false)"

      +> flag "-print" (optional_with_default true bool)
        ~doc:" Print? (default true)"
    )
    (fun symkeyfile symsrc symdst read signb printb () ->
      if signb then (*let () = sign symkeyfile "foo" in*) Deferred.return ()
      else if read then read_key symkeyfile
      else export_key printb symkeyfile symsrc symdst)

let _ = Command.run ~version:"1.0" ~build_info:"Symmetric Key Generator" command
