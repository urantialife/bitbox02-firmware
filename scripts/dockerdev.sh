#!/bin/bash -e
# Copyright 2019 Shift Cryptosecurity AG
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.


DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"

REPO=shiftcrypto/firmware_v2
CONTAINER_NAME=firmware_v2-dev

dockerdev () {
    local mount_dir="$DIR/.."
    local repo_path="$DIR/.."

    if ! docker images | grep -q ${REPO}; then
        echo "No '${REPO}' docker image found! Maybe you need to run
              'docker build --pull -t ${REPO} .'?" >&2
        exit 1
    fi

    # If already running, enter the container.
    if docker ps | grep -q $CONTAINER_NAME; then
        docker exec --user=dockeruser --workdir=$mount_dir -it $CONTAINER_NAME bash
        return
    fi

    if docker ps -a | grep -q $CONTAINER_NAME; then
        docker rm $CONTAINER_NAME
    fi

    docker run \
           --detach \
           --interactive --tty \
           --name=$CONTAINER_NAME \
           -v $repo_path:$mount_dir \
           ${REPO} bash

    # Use same user/group id as on the host, so that files are not created as root in the mounted
    # volume.
    docker exec -it $CONTAINER_NAME groupadd -g `id -g` dockergroup
    docker exec -it $CONTAINER_NAME useradd -u `id -u` -g dockergroup dockeruser

    # Call a second time to enter the container.
    dockerdev
}

if test "$1" == "stop"; then
	if docker ps -a | grep -q $CONTAINER_NAME; then
		docker stop $CONTAINER_NAME
	fi
else
	dockerdev
fi
