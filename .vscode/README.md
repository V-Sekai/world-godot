# README

Tested on msys2 Windows 11, Popos.

## Readme for fire

```bash
scoop install sudo clink
clink autorun install
sudo scoop install msys2 gpg4win lazygit gopass
msys2
pacman -S git python3 ssh-pageant
echo "pacman -S git python3 ssh-pageant" >> ~/.bashrc
echo 'eval $(/usr/bin/ssh-pageant -r -a "/tmp/.ssh-pageant-$USERNAME")' >> ~/.bashrc
echo 'export PATH=/mingw64/bin/:$PATH' >> ~/.bashrc
git config --global user.name "K. S. Ernest (iFire) Lee"
git config --global user.email "ernest.lee@chibifire.com"
mkdir -p ~/.ssh
ssh-keyscan github.com >> ~/.ssh/known_hosts
git clone https://github.com/ingydotnet/git-subrepo ~/git-subrepo
echo 'source ~/git-subrepo/.rc' >> ~/.bashrc
```

## References

https://github.com/nikitalita/lldb-qt-formatters/blob/godot/GodotFormatters.py
