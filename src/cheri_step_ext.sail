/* set misa.X to indicate the presence of a non-standard extension. */

val ext_init : unit -> unit effect {wreg}
function ext_init () = {
  misa->X() = 0b1;
  sccsr->d() = 0b1;
  sccsr->e() = 0b1;
  uccsr->d() = 0b1;
  uccsr->e() = 0b1;
}

/* other hooks are not currently used. */
function ext_fetch_hook(f : FetchResult) -> FetchResult = f

function ext_pre_step_hook()  -> unit = ()
function ext_post_step_hook() -> unit = ()
