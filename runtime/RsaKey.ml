open Core
open Async
open RsaKeyFun



let command =
  Command.async_spec
    ~summary:"generates a private key"
    Command.Spec.(
      empty

      +> flag "-priv" (optional_with_default "private_key1" string)
        ~doc:" File to read private key from (default private_key1)"

      +> flag "-pub" (optional_with_default "public_key1" string)
        ~doc:" File to read public key from (default public_key1)"

      +> flag "-read" (optional_with_default false bool)
        ~doc:" Reading? (default false)"

      +> flag "-sign" (optional_with_default false bool)
        ~doc:" Sign? (default false)"

      +> flag "-print" (optional_with_default true bool)
        ~doc:" Print? (default true)"
    )
    (fun privatekey publickey read signb printb () ->
      if signb then let () = sign privatekey publickey "foo" in Deferred.return ()
      else if read then read_key privatekey publickey
      else export_key printb privatekey publickey)

let _ = Command.run ~version:"1.0" ~build_info:"Private Key Generator" command
