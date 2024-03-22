To type check the program, first you must need the cubical Agda library in `~/.agda`. 
```
mkdir -p ~/.agda/
cd ~/.agda/
git clone https://github.com/agda/cubical
cd cubical
git checkout v0.6
```
To register the cubical library:
```
echo $HOME/.agda/cubical/cubical.agda-lib >> ~/.agda/libraries
```
To type check the formalization:
```
agda index.agda
```
To navigate the formalization, I personally recommend the HTML rendering [here](https://windtfw.com/agda-symmetries/).
If you would like to browse it locally, I recommend the [agda-mode](https://github.com/banacorn/agda-mode-vscode) plugin
on Visual Studio Code. Please look at their README to understand what key bindings are used.
