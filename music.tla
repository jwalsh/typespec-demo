---- MODULE MusicLibrary ----
EXTENDS Naturals, Sequences

CONSTANTS Artist, Album, Track, Playlist

VARIABLES artists, albums, tracks, playlists

vars == <<artists, albums, tracks, playlists>>

ArtistVars == [name: STRING, genre: {STRING}, origin: STRING, members: {STRING}, formedYear: Nat, bio: STRING, images: {STRING}]

AlbumVars == [title: STRING, artist: Artist, releaseYear: Nat, genre: {STRING}, tracks: {Track}, coverArt: STRING]

TrackVars == [title: STRING, artist: Artist, album: Album, duration: Nat, genre: {STRING}, lyrics: STRING, composer: STRING]

PlaylistVars == [name: STRING, owner: STRING, tracks: Seq(Track)]

TypeOK == /\ artists \subseteq [ArtistVars]
          /\ albums \subseteq [AlbumVars]
          /\ tracks \subseteq [TrackVars]
          /\ playlists \subseteq [PlaylistVars]

Init == /\ artists = {}
        /\ albums = {}
        /\ tracks = {}
        /\ playlists = {}

AddArtist == /\ \E artist \in [ArtistVars]:
                 /\ artist.name \notin {a.name: a \in artists}
                 /\ artists' = artists \cup {artist}
                 /\ UNCHANGED <<albums, tracks, playlists>>

AddAlbum == /\ \E album \in [AlbumVars]:
                /\ album.artist \in artists
                /\ album.title \notin {a.title: a \in albums}
                /\ albums' = albums \cup {album}
                /\ UNCHANGED <<artists, tracks, playlists>>

CreatePlaylist == /\ \E playlist \in [PlaylistVars]:
                      /\ playlist.name \notin {p.name: p \in playlists}
                      /\ playlists' = playlists \cup {playlist}
                      /\ UNCHANGED <<artists, albums, tracks>>

AddTrackToPlaylist == /\ \E playlist \in playlists:
                          /\ \E track \in tracks:
                             /\ track \notin {t: t \in Range(playlist.tracks)}
                             /\ playlist.tracks' = Append(playlist.tracks, track)
                          /\ UNCHANGED <<artists, albums, tracks, playlists>>

GetArtistByName(name) == {artist \in artists: artist.name = name}

SearchArtists(query) == {artist \in artists: query \in artist.name}

GetAlbumByTitle(title) == {album \in albums: album.title = title}

GetAlbumsByYear(year) == {album \in albums: album.releaseYear = year}

SearchTracks(query) == {track \in tracks: query \in track.title}

GetTracksLongerThan(seconds) == {track \in tracks: track.duration > seconds}

SearchPlaylists(query) == {playlist \in playlists: query \in playlist.name}

GetPlaylistTracks(name) == {track \in UNION {Range(p.tracks): p \in {pl \in playlists: pl.name = name}}}

Next == \/ AddArtist
        \/ AddAlbum 
        \/ CreatePlaylist
        \/ AddTrackToPlaylist

Spec == Init /\ [][Next]_vars

====