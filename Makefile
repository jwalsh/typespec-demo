# Makefile for TLA+ Docker operations

# Variables
DOCKER_IMAGE_NAME = tla-traffic-light
DOCKER_CONTAINER_NAME = tla-traffic-light-container
TLA_SPEC = TrafficLight.tla

.PHONY: build run stop clean

# Build the Docker image
build:
	docker build -t $(DOCKER_IMAGE_NAME) .

# Run the TLA+ specification in a Docker container
run:
	docker run --name $(DOCKER_CONTAINER_NAME) \
		-v $(PWD):/app \
		$(DOCKER_IMAGE_NAME) \
		java -cp /app/lib/tla2tools.jar tlc2.TLC /app/$(TLA_SPEC)

# Run the TLA+ specification in an interactive bash session
run-interactive:
	docker run -it --name $(DOCKER_CONTAINER_NAME) \
		-v $(PWD):/app \
		$(DOCKER_IMAGE_NAME) \
		/bin/bash

# Stop and remove the Docker container
stop:
	docker stop $(DOCKER_CONTAINER_NAME)
	docker rm $(DOCKER_CONTAINER_NAME)

# Remove the Docker image
clean: stop
	docker rmi $(DOCKER_IMAGE_NAME)

# Run TLC on a specific model (usage: make run-model MODEL=ModelName)
run-model:
	@if [ -z "$(MODEL)" ]; then \
		echo "Please specify a model name. Usage: make run-model MODEL=ModelName"; \
		exit 1; \
	fi
	docker run --rm \
		-v $(PWD):/app \
		$(DOCKER_IMAGE_NAME) \
		java -cp /app/lib/tla2tools.jar tlc2.TLC /app/$(TLA_SPEC) \
		-config /app/$(MODEL).cfg

# Generate TLA+ documentation using tla2tex (if available in tla2tools.jar)
docs:
	docker run --rm \
		-v $(PWD):/app \
		$(DOCKER_IMAGE_NAME) \
		java -cp /app/lib/tla2tools.jar tla2tex.TLA $(TLA_SPEC)

install: # Install the packages
	tsp install

compile: # Compile the project
	tsp compile .

test: # Run the tests
	tsp test .

