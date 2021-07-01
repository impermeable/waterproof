
function unselect_package {
  package=$1

  package_lower=${package//-/_}

  sed -i 's|^Section "'"$package"'".*|Section /o "'"$package"'" Sec_'"$package_lower"'|g' $FILE_SEC_VISIBLE
}
