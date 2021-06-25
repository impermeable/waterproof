
sed -i 's/  InstallDir "C:\\.*/  InstallDir "C:\\cygwin_coq_platform\\home\\runneradmin\\.opam\\_coq-platform_.2021.02.1"/g' coq-platform/windows/Coq.nsi

sed -i '/^OPAM_FILE_WHITELIST\[base\]/ c#OPAM_FILE_WHITELIST\[base\]' coq-platform/windows/create_installer_windows.sh
sed -i '/^OPAM_FILE_WHITELIST\[base-threads\]/ c#OPAM_FILE_WHITELIST\[base-threads\]' coq-platform/windows/create_installer_windows.sh
sed -i '/^OPAM_FILE_WHITELIST\[ppx_deriving\]/ c#OPAM_FILE_WHITELIST\[ppx_deriving\]' coq-platform/windows/create_installer_windows.sh
sed -i '/^OPAM_FILE_WHITELIST\[sexplib0\]/ c#OPAM_FILE_WHITELIST\[sexplib0\]' coq-platform/windows/create_installer_windows.sh
sed -i '/^OPAM_FILE_WHITELIST\[result\]/ c#OPAM_FILE_WHITELIST\[result\]' coq-platform/windows/create_installer_windows.sh
          

sed -i '/^requires(mt,mt_posix)/ c#requires(mt,mt_posix)' .opam/_coq-platform_.2021.02.1/lib/threads/META
sed -i '/^type_of_threads = "posix"/ c#type_of_threads = "none"' .opam/_coq-platform_.2021.02.1/lib/threads/META

sed -i '/      echo "In package '\''$1'\'' the file '\''$file'\'' does not exist"/!b;n;c#      exit 1' coq-platform/windows/create_installer_windows.sh
