Hay varias opciones para ejecutar F\* y seguir la materia.

La opción más fácil es usar OPAM, el manejador de paquetes
de OCaml.

Opción 1 - Vía OPAM
===================

Paso 1.1 - Instalar OPAM y F\*
------------------------------

Primero, instalar OPAM (el manejador de paquetes de OCaml). En Debian/Ubuntu:
`sudo apt install opam`.

Inicializá OPAM con `opam init`. Cuando te pregunte de modificar tu `.profile`
podés contestar "sí" para automáticamente tener en el PATH las cosas que
instales. Si elegís "no", tenés que correr `eval $(opam env)` en cada nueva
shell.

Luego, actualizá los paquetes e instalá F\*. Esto va a tardar varios minutos.

    $ opam update
    $ opam install fstar

Tal vez tengas que instalar los paquetes `libgmp-dev` y `pkg-config` si OPAM no
lo hace.

Asegurate de que se haya instalado una versión reciente de F\*, como mínimo
v2025.08.07.

    $ fstar.exe
    F* version 2025.08.07~dev
    Usage: fstar.exe [options] file.fst
    Use `--help` to see all available options.

Tal vez necesitemos actualizar F\* durante la materia, esto es fácil
con `opam update && opam upgrade`.

Paso 1.2 - Instalar Z3
----------------------

F* necesita del SMT solver Z3, en particular su versión 4.13.3. Para
instalarlo, podés usar el siguiente comando:

    $ wget https://raw.githubusercontent.com/FStarLang/FStar/refs/heads/master/.scripts/get_fstar_z3.sh
    $ sudo bash ./get_fstar_z3.sh /usr/local/bin

También podés instalarlo a algún directorio local en tu PATH (e.g.
`~/bin`), sin necesitar permisos de superusuario.

Paso 1.3 - Instalar extensión de VS Code
----------------------------------------

Instalar la extensión `fstar-vscode-assistant` en VS Code, tanto local
como remoto.

Con todo esto hecho, al abrir un archivo F\* debería verse el coloreo
por sintaxis. Además, apretar `Ctrl+.` en el final del archivo debería
disparar la verificación y mostrar una línea verde a la izquierda del
buffer (si el archivo es correcto).

Opción 2 - Instalación nativa
=============================

Descargá el release
[v2024.08.14](https://github.com/FStarLang/FStar/releases/tag/v2024.08.14)
de F\* correspondiente a tu sistema operativo. Esto incluye un
binario `fstar.exe`, un binario `z3`, entre otras cosas. Luego, agregá
el directorio `bin/` del release a tu `PATH`.

Instalá VS code localmente y seguí el paso 1.4. Con eso debería
quedar todo andando. La única limitación es que no vas a compilar
archivos extraídos debido a una limitación actual (el paquete trae la
librería compilada con _alguna_ versión de OCaml, que seguramente no
va a ser la misma de tu sistema). Esto no es grave.

Opción 3 - GitHub codespaces (versión gratis: máximo 60 horas al mes)
=====================================================================

En este repositorio, clickear el botón `<>Code` y luego `Create
codespace on main`. Esto va a disparar la construcción de un
devcontainer con todo instalado en una VM de GitHub. (Para los curiosos:
la configuración del mismo está en `.devcontainer`.)

La construcción del container tarda bastante tiempo, cerca de **una
hora**.

![](./img/codespace1.png)

Una vez construido, se va abrir una instancia de VS Code en el
navegador. La UI corre en el navegador, localmente, mientras que el
backend (incluyendo F\*, Z3, etc) corre en la VM de GitHub.

Esta instancia de VS Code debería tener la extensión para F\*
instalada desde el comienzo. Sin embargo es posible que haya que
reiniciar (actualizar con F5) para que se active.

![](./img/codespace2.png)

Se puede cerrar la ventana, el codespace seguirá vivo. Se puede volver
a acceder desde la pestaña `<>Code`

![](./img/codespace3.png)

Opción 4 - Compilar desde los fuentes
=====================================

No recomendado... pero los kamikazes pueden seguir las instrucciones de
`INSTALL.md` en el [repositorio de F\*](http://github.com/FStarLang/FStar).
