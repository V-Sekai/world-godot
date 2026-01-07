export RUST_LOG := "log"
export MVSQLITE_DATA_PLANE := "http://192.168.0.39:7000"
export OPERATING_SYSTEM := os()
export EDITOR_TYPE_COMMAND := "run-editor-$OPERATING_SYSTEM"
export PROJECT_PATH := "" # Can be empty

export BUILD_COUNT := "001"
export DOCKER_GOCDA_AGENT_CENTOS_8_GROUPS_GIT := "abcdefgh"  # Example hash
export GODOT_GROUPS_EDITOR_PIPELINE_DEPENDENCY := "dependency_name"

export LABEL_TEMPLATE := "docker-gocd-agent-centos-8-groups_${DOCKER_GOCDA_AGENT_CENTOS_8_GROUPS_GIT:0:8}.$BUILD_COUNT"
export GROUPS_LABEL_TEMPLATE := "groups-4.3.$GODOT_GROUPS_EDITOR_PIPELINE_DEPENDENCY.$BUILD_COUNT"
export GODOT_STATUS := "groups-4.3"
export GIT_URL_DOCKER := "https://github.com/V-Sekai/docker-groups.git"
export GIT_URL_VSEKAI := "https://github.com/V-Sekai/v-sekai-game.git"
export WORLD_PWD := invocation_directory()
export ANDROID_NDK_VERSION := "23.2.8568313"
export arm64toolchain := "https://github.com/godotengine/buildroot/releases/download/godot-2023.08.x-4/aarch64-godot-linux-gnu_sdk-buildroot.tar.bz2"
export cmdlinetools := "commandlinetools-linux-11076708_latest.zip"

export CUSTOM_SUFFIX := "vsekai"
export ARM64_ROOT := WORLD_PWD + "/aarch64-godot-linux-gnu_sdk-buildroot"
export ANDROID_SDK_ROOT := WORLD_PWD + "/android_sdk"
export ANDROID_HOME := ANDROID_SDK_ROOT
export JAVA_HOME := WORLD_PWD + "/jdk"
export VULKAN_SDK_ROOT := WORLD_PWD + "/vulkan_sdk/"
export EMSDK_ROOT := WORLD_PWD + "/emsdk"
export OSXCROSS_ROOT := WORLD_PWD + "/osxcross"
export MINGW_PREFIX := WORLD_PWD + "/mingw"

default:
    @just --list

run-all:
    just fetch-openjdk
    just setup-android-sdk
    just setup-emscripten
    just fetch-llvm-mingw
    just build-osxcross
    just fetch-vulkan-sdk
    just build-platform-target macos template_release
    echo "run-all: Success!"

fetch-llvm-mingw-macos:
    #!/usr/bin/env bash
    if [ ! -d "${MINGW_PREFIX}" ]; then
        cd $WORLD_PWD
        mkdir -p ${MINGW_PREFIX}
        curl -o llvm-mingw.tar.xz -L https://github.com/mstorsjo/llvm-mingw/releases/download/20241030/llvm-mingw-20241030-ucrt-macos-universal.tar.xz
        tar --dereference -xf llvm-mingw.tar.xz -C ${MINGW_PREFIX} --strip 1
        rm -rf llvm-mingw.tar.xz
    fi


fetch-llvm-mingw:
    #!/usr/bin/env bash
    if [ ! -d "${MINGW_PREFIX}" ]; then
        cd $WORLD_PWD
        mkdir -p ${MINGW_PREFIX}
        curl -o llvm-mingw.tar.xz -L https://github.com/mstorsjo/llvm-mingw/releases/download/20240917/llvm-mingw-20240917-ucrt-ubuntu-20.04-x86_64.tar.xz
        tar --dereference -xf llvm-mingw.tar.xz -C ${MINGW_PREFIX} --strip 1
        rm -rf llvm-mingw.tar.xz
    fi

setup-d3d12:
    #!/usr/bin/env bash
    cd $WORLD_PWD/godot
    if [ ! -d "bin/build_deps/mesa" ] || [ ! -d "bin/build_deps/agility_sdk" ]; then
        python3 misc/scripts/install_d3d12_sdk_windows.py --mingw_prefix=${MINGW_PREFIX}
    fi

fetch-openjdk:
    #!/usr/bin/env bash
    if [ ! -d "${JAVA_HOME}" ]; then
        curl --fail --location --silent --show-error "https://github.com/adoptium/temurin17-binaries/releases/download/jdk-17.0.11%2B9/OpenJDK17U-jdk_$(uname -m | sed -e s/86_//g)_linux_hotspot_17.0.11_9.tar.gz" --output jdk.tar.gz
        mkdir -p {{JAVA_HOME}}
        tar --dereference -xf jdk.tar.gz -C {{JAVA_HOME}} --strip 1
        rm -rf jdk.tar.gz
    fi

fetch-vulkan-sdk:
    #!/usr/bin/env bash
    if [ ! -d "${VULKAN_SDK_ROOT}" ]; then
        curl -L "https://github.com/godotengine/moltenvk-osxcross/releases/download/vulkan-sdk-1.3.283.0-2/MoltenVK-all.tar" -o vulkan-sdk.zip
        mkdir -p ${VULKAN_SDK_ROOT}
        tar -xf vulkan-sdk.zip -C {{VULKAN_SDK_ROOT}}
        rm vulkan-sdk.zip
    fi

setup-android-sdk:
    #!/usr/bin/env bash
    if [ ! -d "${ANDROID_SDK_ROOT}" ]; then
        mkdir -p {{ANDROID_SDK_ROOT}}
        if [ ! -d "{{WORLD_PWD}}/{{cmdlinetools}}" ]; then
            curl -LO https://dl.google.com/android/repository/{{cmdlinetools}} -o {{WORLD_PWD}}/{{cmdlinetools}}
            cd {{WORLD_PWD}} && unzip -o {{WORLD_PWD}}/{{cmdlinetools}}
            rm {{WORLD_PWD}}/{{cmdlinetools}}
            yes | {{WORLD_PWD}}/cmdline-tools/bin/sdkmanager --sdk_root={{ANDROID_SDK_ROOT}} --licenses
            yes | {{WORLD_PWD}}/cmdline-tools/bin/sdkmanager --sdk_root={{ANDROID_SDK_ROOT}} "ndk;{{ANDROID_NDK_VERSION}}" 'cmdline-tools;latest' 'build-tools;34.0.0' 'platforms;android-34' 'cmake;3.22.1'
        fi
    fi
setup-rust:
    #!/usr/bin/env bash
    cd $WORLD_PWD
    if [ ! -d "${RUST_ROOT}" ]; then
        mkdir -p ${RUST_ROOT}
        curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain nightly --no-modify-path
        . "$HOME/.cargo/env"
        rustup default nightly
        rustup target add aarch64-linux-android x86_64-linux-android x86_64-unknown-linux-gnu aarch64-apple-ios x86_64-apple-ios x86_64-apple-darwin aarch64-apple-darwin x86_64-pc-windows-gnu x86_64-pc-windows-msvc wasm32-wasi
    fi

setup-emscripten:
    #!/usr/bin/env bash
    if [ ! -d "${EMSDK_ROOT}" ]; then
        git clone https://github.com/emscripten-core/emsdk.git $EMSDK_ROOT
        cd $EMSDK_ROOT
        ./emsdk install 4.0.11
        ./emsdk activate 4.0.11
    fi

setup-arm64:
    #!/usr/bin/env bash
    curl -LO "${arm64toolchain}" && \
    tar xf aarch64-godot-linux-gnu_sdk-buildroot.tar.bz2 && \
    rm -f aarch64-godot-linux-gnu_sdk-buildroot.tar.bz2 && \
    cd aarch64-godot-linux-gnu_sdk-buildroot && \
    ./relocate-sdk.sh

deploy_osxcross:
    #!/usr/bin/env bash
    git clone https://github.com/tpoechtrager/osxcross.git || true
    cd osxcross
    ./tools/gen_sdk_package.sh 

build-osxcross:
    #!/usr/bin/env bash
    if [ ! -d "${OSXCROSS_ROOT}" ]; then
        git clone https://github.com/tpoechtrager/osxcross.git 
        curl -o $OSXCROSS_ROOT/tarballs/MacOSX15.0.sdk.tar.xz -L https://github.com/V-Sekai/world/releases/download/v0.0.1/MacOSX15.0.sdk.tar.xz
        ls -l $OSXCROSS_ROOT/tarballs/
        cd $OSXCROSS_ROOT && UNATTENDED=1 ./build.sh && ./build_compiler_rt.sh
    fi

nil:
    echo "nil: Suceeded."

install_packages:
    if dnf >/dev/null 2>&1; then \
        dnf install -y hyperfine vulkan xz bzip2 file gcc gcc-c++ zlib-devel libmpc-devel mpfr-devel gmp-devel clang just parallel scons mold pkgconfig libX11-devel libXcursor-devel libXrandr-devel libXinerama-devel libXi-devel wayland-devel mesa-libGL-devel mesa-libGLU-devel alsa-lib-devel pulseaudio-libs-devel libudev-devel libstdc++-static libatomic-static cmake ccache patch libxml2-devel openssl openssl-devel git unzip; \
    else \
        sudo apt install -y build-essential hyperfine vulkan-tools xz-utils bzip2 file gcc zlib1g-dev libmpc-dev libmpfr-dev libgmp-dev clang just parallel scons mold pkg-config libx11-dev libxcursor-dev libxrandr-dev libxinerama-dev libxi-dev libwayland-dev libgl1-mesa-dev libglu1-mesa-dev libasound2-dev libpulse-dev libudev-dev cmake ccache patch libxml2-dev openssl libssl-dev git unzip; \
    fi

copy_binaries:
    cp templates/windows_release_x86_64.exe export_windows/v_sekai_windows.exe
    cp templates/linux_release.x86_64 export_linuxbsd/v_sekai_linuxbsd

prepare_exports:
    rm -rf export_windows export_linuxbsd
    mkdir export_windows export_linuxbsd

generate_build_constants:
    echo "## AUTOGENERATED BY BUILD" > v/addons/vsk_version/build_constants.gd
    echo "" >> v/addons/vsk_version/build_constants.gd
    echo "const BUILD_LABEL = \"$GROUPS_LABEL_TEMPLATE\"" >> v/addons/vsk_version/build_constants.gd
    echo "const BUILD_DATE_STR = \"$(shell date --utc --iso=seconds)\"" >> v/addons/vsk_version/build_constants.gd
    echo "const BUILD_UNIX_TIME = $(shell date +%s)" >> v/addons/vsk_version/build_constants.gd

build-platform-target platform target arch="auto" precision="double" osx_bundle="yes" extra_options="":
    #!/usr/bin/env bash
    set -o xtrace
    cd $WORLD_PWD
    if [[ "{{platform}}" == "web" && -d "$EMSDK_ROOT" ]]; then
        source "$EMSDK_ROOT/emsdk_env.sh"
    fi
    HOST_ARCH=$( uname -m )
    echo "HOST ARCHITECTURE: ${HOST_ARCH}"
    if [[ "{{arch}}" == "arm64" && ${HOST_ARCH} == 'x86_64' ]]; then
        rename 'aarch64-godot-linux-gnu-' '' ${ARM64_ROOT}/bin/*;
        export PATH="$ARM64_ROOT/bin:$PATH";
    fi
    cd godot
    case "{{platform}}" in
        macos)
            if [ "$(uname)" = "Darwin" ]; then
                unset OSXCROSS_ROOT
            else
                export PATH=${OSXCROSS_ROOT}/target/bin/:$PATH
            fi
            scons platform=macos \
                    arch={{arch}} \
                    werror=no \
                    compiledb=yes \
                    precision={{precision}} \
                    target={{target}} \
                    test=yes \
                    vulkan=no \
                    vulkan_sdk_path=$VULKAN_SDK_ROOT/MoltenVK/MoltenVK/static/MoltenVK.xcframework \
                    osxcross_sdk=darwin24 \
                    generate_bundle={{osx_bundle}} \
                    debug_symbols=yes \
                    separate_debug_symbols=yes \
                    extra_suffix=$CUSTOM_SUFFIX \
                    {{extra_options}}
            ;;
        windows)
            scons platform=windows \
                arch={{arch}} \
                werror=no \
                compiledb=yes \
                precision={{precision}} \
                target={{target}} \
                test=yes \
                use_llvm=yes \
                use_mingw=yes \
                debug_symbols=yes \
                separate_debug_symbols=yes \
                extra_suffix=$CUSTOM_SUFFIX \
                {{extra_options}}
            ;;
        android)
            scons platform=android \
                    arch={{arch}} \
                    werror=no \
                    compiledb=yes \
                    precision={{precision}} \
                    target={{target}} \
                    test=yes \
                    extra_suffix=$CUSTOM_SUFFIX \
                    {{extra_options}} \
                    #debug_symbols=yes    # Editor build runs out of space in Github Runner
            ;;
        linuxbsd)
            DEBUG_SYMBOLS=""
            if [[ "$(just is-github-actions)" == "true" && "{{target}}" == "editor" ]]; then
                # Disable debug symbols for editor builds in CI to save disk space
                DEBUG_SYMBOLS="debug_symbols=no"
            else
                DEBUG_SYMBOLS="debug_symbols=yes separate_debug_symbols=yes"
            fi
            scons platform=linuxbsd \
                    arch={{arch}} \
                    werror=no \
                    compiledb=yes \
                    precision={{precision}} \
                    target={{target}} \
                    test=yes \
                    $DEBUG_SYMBOLS \
                    extra_suffix=$CUSTOM_SUFFIX \
                    {{extra_options}}
            ;;
        web)
            scons platform=web \
                    arch={{arch}} \
                    werror=no \
                    optimize=size_extra \
                    compiledb=yes \
                    precision={{precision}} \
                    target={{target}} \
                    test=yes \
                    dlink_enabled=yes \
                    debug_symbols=no \
                    disable_exceptions=yes \
                    extra_suffix=$CUSTOM_SUFFIX \
                    {{extra_options}}
            ;;
        ios)
            if [ "$(uname)" = "Darwin" ]; then
                unset OSXCROSS_ROOT
            else
                export PATH=${OSXCROSS_ROOT}/target/bin/:$PATH
            fi
            scons platform=ios \
                    arch={{arch}} \
                    werror=no \
                    compiledb=yes \
                    precision={{precision}} \
                    target={{target}} \
                    test=yes \
                    vulkan=no \
                    vulkan_sdk_path=$VULKAN_SDK_ROOT/MoltenVK/MoltenVK/static/MoltenVK.xcframework \
                    osxcross_sdk=darwin24 \
                    generate_bundle={{osx_bundle}} \
                    debug_symbols=yes \
                    separate_debug_symbols=yes \
                    extra_suffix=$CUSTOM_SUFFIX \
                    {{extra_options}}
            ;;
        *)
            echo "Unsupported platform: {{platform}}"
            exit 1
            ;;
    esac
    just handle-special-cases {{platform}} {{target}}

    # Remove intermediate build files before copy
    rm -rf $WORLD_PWD/godot/bin/obj

    # In Github runner copy editor as hardlink to save space
    if [[ "$(just is-github-actions)" == "true" ]]; then COPYSYM="-l"; else COPYSYM=""; fi

    if [[ "{{target}}" == "editor" ]]; then
        mkdir -p $WORLD_PWD/editors
        cp $COPYSYM -rf $WORLD_PWD/godot/bin/* $WORLD_PWD/editors
    elif [[ "{{target}}" =~ template_* && \
            "{{platform}}" =~ ^(mac|i)os && \
            "{{osx_bundle}}" == "no" ]]; then
        # don't copy files to $WORLD_PWD/tpz
        true
    elif [[ "{{target}}" =~ template_* ]]; then
        mkdir -p $WORLD_PWD/tpz
        cp -rf $WORLD_PWD/godot/bin/* $WORLD_PWD/tpz
    fi

build-platform-templates platform arch="auto" precision="double":
    # Bundle all on last command with osx_bundle
    just build-platform-target {{platform}} template_debug {{arch}} {{precision}} "no"
    just build-platform-target {{platform}} template_release {{arch}} {{precision}} "yes"

all-build-platform-target:
    #!/usr/bin/env bash
    parallel --ungroup --jobs 1 'just build-platform-target {1} {2}' \
    ::: windows linuxbsd macos android web \
    ::: editor template_debug template_release

handle-special-cases platform target:
    #!/usr/bin/env bash
    case "{{platform}}" in
        android)
            just handle-android {{target}} \
            ;;
        macos)
            just handle-macos {{target}} \
            ;;
    esac

handle-android target:
    #!/usr/bin/env bash
    cd godot
    if [ "{{target}}" = "editor" ]; then
        cd platform/android/java
        ./gradlew generateGodotEditor
        ./gradlew generateGodotHorizonOSEditor
        cd ../../..
        ls -l bin/android_editor_builds/
    elif [ "{{target}}" = "template_release" ] || [ "{{target}}" = "template_debug" ]; then
        cd platform/android/java
        ./gradlew generateGodotTemplates
        cd ../../..
        ls -l bin/
    fi

handle-macos target:
    #!/usr/bin/env bash
    cd godot
    if [ "{{target}}" = "editor" ]; then
        chmod +x ./bin/*.app/Contents/MacOS/* || echo "Could not set execute permission on editor"
    fi

package-tpz folder tpzname versionpy precision="double":
    #!/usr/bin/env bash
    cd {{folder}}
    rm *.arm64.a || true  # Avoid Godot error on template import
    for file in *; do \
        filename=$( echo ${file} \
          | sed 's/\(godot.\|.double\|.template\|.llvm\|.wasm32\)//g' \
          | sed 's/linuxbsd/linux/;s/.console/_console/' \
          | sed 's/^web\(_debug\|_release\)\.\(dlink\)\(.*\)/web_\2\1\3/' \
          | sed 's/\(windows_[a-z]*\)\./\1_/' \
        ) \
        && echo -e "Renaming ${file} to \n ${filename}" \
        && mv ${file} ${filename}
    done
    cd ..
    cat {{versionpy}} | tr -d ' ' | tr -s '\n' ' ' \
      | sed -E 's/.*major=([0-9]).minor=([0-9]).*status=\"([a-z]*)\".*/\1.\2.\3/' \
      > {{folder}}/version.txt
    if [ "{{precision}}" = "double" ]; then
      echo ".double" >> {{folder}}/version.txt
    fi
    echo "Godot TPZ Version: $( cat {{folder}}/version.txt )"
    mkdir -p tpz_temp && mv {{folder}} tpz_temp/templates && cd tpz_temp \
      && zip -r ../{{tpzname}}.tpz templates && cd ..
    rm -r tpz_temp

is-github-actions:
    #!/usr/bin/env bash
    if [[ "$CI" == "true" && "$GITHUB_ACTIONS" == "true" ]]; then
      echo "true"
    else
      echo "false"
    fi
