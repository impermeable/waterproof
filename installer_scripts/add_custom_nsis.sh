#######################################
# Adds custom package to NSIS installer configuration files.
# Globals:
#   $FILE_SEC_VISIBLE:      Location of the NSIS include file for the visible installer sections.
#   $FILE_STRINGS:          Location of the NSIS include file for strings such as the sections descriptions.
#   $FILE_SEC_DESCRIPTIONS: Location of the NSIS include file for section descriptions.
#   $DIR_TARGET:            Location of directory containing all generated NSIS include files.
# Arguments:
#   $1 Package name.
#   $2 Relative installed path location from Opam switch in Linux formatting.
#   $3 Package description to be displayed in installer.
# Outputs:
#   Writes necessary .nsh files such that package $1 is installed in complience with the Coq platform setup.
#######################################
function add_custom_package {
  echo "Adding custom package $1."
  
  # Change all non ascii characters to _
  package_name_clean=${1//[^a-zA-Z0-9]/_}
  
  #Add to file dependencies_visible_deselection.nsh
  #${SectionVisibleDeSelect} ${Sec_coq_serapi} ${Sec_coq} 'coq_serapi' 'coq'
  #Add to file dependencies_visible_selection.nsh
  #${SectionVisibleSelect} ${Sec_coq_serapi} ${Sec_coq} 'coq_serapi' 'coq'

  # Add files paths to file files_$package_name_clean.nsh to install by the installer
  # Specify installation directory
  install_dir=$(sed 's:/:\\:g' <<< $2)
  echo Adding $2 in $(cygpath $OPAM_PREFIX)

  touch "$DIR_TARGET/files_$package_name_clean.nsh" # create empty file
  add_foler_recursively "$(cygpath $OPAM_PREFIX)/" $2 "files_$package_name_clean" # add files from in $2 to files_$package_name_clean.nsh

  # Add files_$1.nsh to sections_visible.nsh
  echo "Section \"$package_name_clean\" Sec_$package_name_clean" >> "$FILE_SEC_VISIBLE"
  echo 'SetOutPath "$INSTDIR\"' >> "$FILE_SEC_VISIBLE"
  echo "!include \"files_$package_name_clean.nsh\"" >> "$FILE_SEC_VISIBLE"
  echo "SectionEnd" >> "$FILE_SEC_VISIBLE"

  # Add description file section_descriptions.nsh
  echo 'LangString DESC_'"$package_name_clean"' ${LANG_ENGLISH} "'"$3"'"' >> "$FILE_STRINGS"
  echo '!insertmacro MUI_DESCRIPTION_TEXT ${Sec_'"$package_name_clean"'} $(DESC_'"$package_name_clean"')' >> "$FILE_SEC_DESCRIPTIONS"
  
  # Finished
  echo "Done adding custom package $1."
}
