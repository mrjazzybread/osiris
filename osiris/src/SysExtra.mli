open FilenameExtra

(**[ensure_directory_exists filename] ensures that [filename] exists and is a
   directory. It creates this directory, and its parent directories, if
   needed. It is analogous to [mkdir -p]. *)
val ensure_directory_exists : filename -> unit

(**[ensure_directory_exists filename] ensures that the parent directory of the
   file name [filename] exists. *)
val ensure_parent_directory_exists : filename -> unit
