# TypeSpec Demo

This repository contains a collection of TypeSpec models, specifications, and examples showcasing various features and use cases of the TypeSpec language.

## Contents

### Specifications

- **TrafficLight.tla**: A TLA+ specification modeling a traffic light system.
- **music.tla** and **music.tsp**: TLA+ specification and TypeSpec model for a music library, including artists, albums, tracks, and playlists.

### TypeSpec Models

- **moria.tsp**: Models for items, equipment, and other entities in a fantasy RPG game, such as weapons, armor, potions, and valuables.
- **pokemon.tsp**: Models representing Pokémon species, including their types, stats, evolutions, and other data.
- **recipes.tsp**: Models for recipes, ingredients, units of measurement, and a recipe database interface.
- **url_shortener.tsp**: Models and interface for a URL shortening service, including operations for shortening URLs and retrieving original URLs.

### Docker and Build Files

- **Dockerfile**: A Dockerfile for running TLA+ specifications in a Docker container.
- **Makefile**: A Makefile with targets for building and running the TLA+ Docker image, as well as other utility tasks.

## Prerequisites

- [TypeSpec Compiler](https://typespec.io/docs/installation) (version 0.56.0 or later)
- [TLA+ Tools](https://github.com/tlaplus/tlaplus/releases) (for running TLA+ specifications)
- Docker (for running the TLA+ specifications in a container)

## Usage

1. Clone this repository: `git clone https://github.com/yourusername/typespec-demo.git`
2. Navigate to the project directory: `cd typespec-demo`
3. Install TypeSpec dependencies: `tsp install`
4. Compile the TypeSpec models: `tsp compile .`
5. Run the TLA+ specifications:
   - Using Docker: `make run` or `make run-model MODEL=ModelName`
   - Locally (if TLA+ Tools is installed): `tlc2.TLC TrafficLight.tla` or `tlc2.TLC music.tla`

For more details on running and using the individual models and specifications, refer to the respective files and the TypeSpec documentation.

## Contributing

Contributions are welcome! If you find any issues or have suggestions for improvements, please open an issue or submit a pull request.

## License

This project is licensed under the [MIT License](LICENSE).
