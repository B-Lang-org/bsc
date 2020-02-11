Vagrant.configure("2") do |config|
  config.vm.box = "hashicorp/bionic64"

  # Map the current directory into its conventional location, but use rsync
  # rather than Virtualbox shared folders. This leaves the guest free to create
  # hardlinks, which vbox doesn't support; on the other hand, it means we must
  # manually extract build artifacts or lose them.
  #
  # Note that we are *deliberately* exposing the .git subdirectory to the VM.
  # The build process needs access to it to generate version strings.
  config.vm.synced_folder ".", "/vagrant", type: "rsync"

  config.vm.synced_folder "vagrant-out", "/vagrant/inst", create: true

  config.vm.provider "virtualbox" do |vb|
    vb.memory = 4096
    vb.cpus = 4
  end

  config.vm.provision :shell, path: "util/vagrant/provision.sh"
end
