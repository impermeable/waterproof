!macro customInstall
    File '/oname=$PLUGINSDIR\Coq-Waterproof-installer.exe' '${PROJECT_DIR}\Coq-Waterproof-installer.exe'
    ExecWait '"$PLUGINSDIR\Coq-Waterproof-installer.exe"' $0
    DetailPrint "installer result: $0"
    Delete "$PLUGINSDIR\coq-platform-installer.exe"
!macroend

