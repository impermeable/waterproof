#!/usr/bin/bash

function install_package {
  echo "Installing Github package $1/$2."
  # Clone repo
  git clone https://github.com/$1/$2

  # Build and install repository
  cd $repo_name
  make
  make install
  cd ..
  rm -rf $repo_name
  echo "Finished installing Github package $1/$2."
}

mkdir github_packages

config_file="packages.cfg"
# Read all lines not starting with #
grep -v '^#' $config_file | while read -r line ; do
  eval "package_info=($line)"

  package_name=${package_info[1]}
  package_selected=${package_info[2]}
  
  if [ "$package_selected" == "UNSELECTED" ] ; then
    sed -i '/^###### Create the NSIS installer #####/a unselect_package '"${package_info[1]}" windows/create_installer_windows.sh
  fi
  
  if [[ $line =~ ^GITHUB* ]] ; then
    package_path=${package_info[3]}
    package_description=${package_info[4]}
    owner_name=${package_info[5]}
    repo_name=${package_info[6]}

    cd github_packages
    install_package $owner_name $repo_name
    cd ..

    # Inject install code into installer script
    sed -i '/^# This ensures people get what they expect./a add_custom_package "'"${package_name}"'" "'"${package_path}"'" "'"${package_description}"'"' windows/create_installer_windows.sh
  elif [[ $line =~ ^OPAM* ]] ; then
    opam install -y $package_name
  fi
done

rmdir github_packages

# Inject install steps into installer script
sed -i '/^# This ensures people get what they expect./a source add_custom_nsis.sh' windows/create_installer_windows.sh

sed -i '/^###### Create the NSIS installer #####/a source unselect_packages.sh' windows/create_installer_windows.sh
