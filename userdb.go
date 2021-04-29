// Copyright 2017-2019 Dale Farnsworth. All rights reserved.

// Dale Farnsworth
// 1007 W Mendoza Ave
// Mesa, AZ  85210
// USA
//
// dale@farnsworth.org

// This file is part of UserDB.
//
// UserDB is free software: you can redistribute it and/or modify
// it under the terms of version 3 of the GNU Lesser General Public
// License as published by the Free Software Foundation.
//
// UserDB is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with UserDB.  If not, see <http://www.gnu.org/licenses/>.

package userdb

import (
	"bufio"
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"io/ioutil"
	"net/http"
	"os"
	"sort"
	"strconv"
	"strings"
	"time"

	"github.com/dalefarnsworth-dmr/debug"
)

var specialUsersURL = "http://registry.dstar.su/api/node.php"
var fixedUsersURL = "https://raw.githubusercontent.com/travisgoodspeed/md380tools/master/db/fixed.csv"
var radioidUsersURL = "https://database.radioid.net/static/users.json"
var reflectorUsersURL = "http://registry.dstar.su/reflector.db"
var overrideUsersURL = "https://farnsworth.org/dale/md380tools/userdb/override.csv"
var pd1wpUsersURL = "https://farnsworth.org/dale/md380tools/userdb/pd1wp.csv"
var curatedUsersURL = "https://farnsworth.org/dale/md380tools/userdb/curated.csv"

var transportTimeout = 20
var clientTimeout = 300

var tr = &http.Transport{
	TLSHandshakeTimeout:   time.Duration(transportTimeout) * time.Second,
	ResponseHeaderTimeout: time.Duration(transportTimeout) * time.Second,
}

var client = &http.Client{
	Transport: tr,
	Timeout:   time.Duration(clientTimeout) * time.Second,
}

// Options - Optional changes to the user entries in the database
type Options struct {
	AbbrevCountries    bool
	AbbrevDirections   bool
	AbbrevStates       bool
	CheckTitleCase     bool
	FixRomanNumerals   bool
	FixStateCountries  bool
	MiscChanges        bool
	RemoveCallFromNick bool
	RemoveDupSurnames  bool
	RemoveMatchingNick bool
	RemoveRepeats      bool
	TitleCase          bool
	FilterByCountries  bool
}

// User - A structure holding information about a user in the databae
type User struct {
	ID          int
	Callsign    string
	Name        string
	City        string
	State       string
	Nick        string
	Country     string
	fullCountry string
}

// UsersDB - A structure holding information about the database of DMR users
type UsersDB struct {
	filename          string
	getUsersFuncs     []func() ([]*User, error)
	options           *Options
	progressCallback  func(progressCounter int) error
	progressFunc      func() error
	progressIncrement int
	progressCounter   int
	users             []*User
	IncludedCountries map[string]bool
}

var DefaultOptions = &Options{
	AbbrevCountries:    true,
	AbbrevDirections:   true,
	AbbrevStates:       true,
	CheckTitleCase:     true,
	FixRomanNumerals:   true,
	FixStateCountries:  true,
	MiscChanges:        true,
	RemoveCallFromNick: true,
	RemoveDupSurnames:  true,
	RemoveMatchingNick: true,
	RemoveRepeats:      true,
	TitleCase:          true,
}

var downloadMergedUsersFuncs = []func() ([]*User, error){
	downloadpd1wpUsers,
	downloadFixedUsers,
	downloadReflectorUsers,
	downloadRadioidUsers,
	downloadpd1wpUsersNames,
	downloadOverrideUsers,
}

var downloadCuratedUsersFuncs = []func() ([]*User, error){
	downloadCuratedUsers,
}

var stateAbbreviations map[string]map[string]string
var titleCaseMap map[string]string
var reverseCountryAbbrevs map[string]string
var reverseStateAbbrevs map[string]map[string]string

func init() {
	stateAbbreviations = make(map[string]map[string]string)
	titleCaseMap = make(map[string]string)
	reverseCountryAbbrevs = make(map[string]string)
	reverseStateAbbrevs = make(map[string]map[string]string)

	// make reverse country abbreviations
	for c, ac := range countryAbbreviations {
		existing := reverseCountryAbbrevs[ac]
		if existing != "" {
			l.Fatalf("%s has abbreviations %s & %s", c, existing, ac)

		}
		reverseCountryAbbrevs[ac] = c
	}

	// add alternate country spellings
	for c, ac := range extraCountryAbbreviations {
		countryAbbreviations[c] = ac
	}

	// Make country keys lower case
	lowerCountryAbbreviations := make(map[string]string)
	for country, ac := range countryAbbreviations {
		lowerCountryAbbreviations[strings.ToLower(country)] = ac
	}
	countryAbbreviations = lowerCountryAbbreviations

	lowerStateAbbreviationsByCountry := make(map[string]map[string]string)
	for country, sa := range stateAbbreviationsByCountry {
		lowerStateAbbreviationsByCountry[strings.ToLower(country)] = sa
	}
	stateAbbreviationsByCountry = lowerStateAbbreviationsByCountry

	// make reverse state abbreviations
	for country, stateAbbreviations := range stateAbbreviationsByCountry {
		for s, as := range stateAbbreviations {
			country = strings.ToLower(country)
			existing := reverseStateAbbrevs[country][as]
			if existing != "" {
				l.Fatalf("%s has abbreviations %s & %s", as, existing, s)
			}
			if reverseStateAbbrevs[country] == nil {
				reverseStateAbbrevs[country] = make(map[string]string)
			}
			reverseStateAbbrevs[country][as] = s
		}
	}

	// add alternate state spellings
	for country, cMap := range extraStateAbbreviationsByCountry {
		country = strings.ToLower(country)
		for s, sa := range cMap {
			stateAbbreviationsByCountry[country][s] = sa
		}
	}

	// create state abbreviations[country][state]
	for country, stateAbbrevs := range stateAbbreviationsByCountry {
		country = strings.ToLower(country)
		for state, abbrev := range stateAbbrevs {
			state = strings.ToLower(state)
			if stateAbbreviations[country] == nil {
				stateAbbreviations[country] = make(map[string]string)
			}
			stateAbbreviations[country][state] = abbrev
		}
	}

	for _, word := range titleCaseWords {
		titleCaseMap[word] = strings.Title(word)
	}
}

// CuratedDB - Instantiate a new users db and download curated users
func NewCuratedDB() (*UsersDB, error) {
	db := &UsersDB{
		progressFunc: func() error { return nil },
	}

	db.SetOptions(DefaultOptions)
	db.getUsersFuncs = downloadCuratedUsersFuncs
	err := db.getUsers()
	if err != nil {
		return nil, err
	}

	return db, nil
}

// MergedDB - Instantiate a new users db ready to merge various sources
func NewMergedDB() (*UsersDB, error) {
	db := &UsersDB{
		progressFunc: func() error { return nil },
	}

	db.SetOptions(DefaultOptions)
	db.getUsersFuncs = downloadMergedUsersFuncs
	err := db.getUsers()
	if err != nil {
		return nil, err
	}

	return db, nil
}

// FileDB - Instantiate a new userdb ready to read from a file
func NewFileDB(path string) (*UsersDB, error) {
	db := &UsersDB{
		progressFunc: func() error { return nil },
	}

	db.SetOptions(DefaultOptions)
	db.getUsersFuncs = readFileUsersFuncs(path)
	err := db.getUsers()
	if err != nil {
		return nil, err
	}

	return db, nil
}

// SetOptions - Set the the desired options for processing the DMR database
func (db *UsersDB) SetOptions(options *Options) {
	db.options = options
}

// SetProgressCallback - Set callback function for progress of db operations.
func (db *UsersDB) SetProgressCallback(fcn func(int) error) {
	db.progressCallback = fcn
}

func (db *UsersDB) setMaxProgressCount(max int) {
	db.progressFunc = func() error { return nil }
	if db.progressCallback != nil {
		db.progressIncrement = MaxProgress / max * 99 / 100
		db.progressCounter = 0
		db.progressFunc = func() error {
			db.progressCounter += db.progressIncrement
			curProgress := db.progressCounter
			if curProgress > MaxProgress {
				curProgress = MaxProgress
			}

			return db.progressCallback(db.progressCounter)
		}
		db.progressCallback(db.progressCounter)
	}
}

func (db *UsersDB) finalProgress() {
	//fmt.Fprintf(os.Stderr, "\nprogressMax %d\n", db.progressCounter/db.progressIncrement)
	if db.progressCallback != nil {
		db.progressCallback(MaxProgress)
	}
}

// Minimum and maximum vallues of the progress counter
const (
	MinProgress = 0
	MaxProgress = 1000000
)

const (
	MaxUV380Users = 122197
)

func abbreviateCountry(country string) string {
	abbrev, ok := countryAbbreviations[strings.ToLower(country)]
	if !ok {
		abbrev = country
	}

	return abbrev
}

func unAbbreviateCountry(abbrev string) string {
	country, ok := reverseCountryAbbrevs[abbrev]
	if !ok {
		country = abbrev
	}

	return country
}

func abbreviateState(state, country string) string {
	abbrev, ok := stateAbbreviations[strings.ToLower(country)][strings.ToLower(state)]
	if !ok {
		abbrev = state
	}

	return abbrev
}

func unAbbreviateState(abbrev, country string) string {
	state, ok := reverseStateAbbrevs[strings.ToLower(country)][abbrev]
	if !ok {
		state = abbrev
	}

	return state
}

func (u *User) amend(options *Options) {
	u.fixCallsigns()

	if options.RemoveDupSurnames {
		u.Name = removeDupSurnames(u.Name)
	}
	if options.RemoveRepeats {
		u.Name = removeRepeats(u.Name)
		u.City = removeRepeats(u.City)
		u.State = removeRepeats(u.State)
		u.Nick = removeRepeats(u.Nick)
		u.Country = removeRepeats(u.Country)
	}
	if options.TitleCase {
		u.Name = titleCase(u.Name)
		u.City = titleCase(u.City)
		u.State = titleCase(u.State)
		u.Country = titleCase(u.Country)
	}
	if options.RemoveMatchingNick {
		u.removeMatchingNicks()
	} else {
		u.addNicks()
	}
	if options.FixStateCountries {
		u.fixStateCountries()
	}
	if options.AbbrevCountries {
		u.Country = abbreviateCountry(u.Country)
	} else {
		u.Country = unAbbreviateCountry(u.Country)
	}
	u.fullCountry = unAbbreviateCountry(u.Country)
	if options.AbbrevStates {
		u.State = abbreviateState(u.State, u.fullCountry)
	} else {
		u.State = unAbbreviateState(u.State, u.fullCountry)
	}
	if options.AbbrevDirections {
		u.City = abbreviateDirections(u.City)
		u.State = abbreviateDirections(u.State)
		u.Country = abbreviateDirections(u.Country)
	}
	if options.RemoveCallFromNick {
		u.Nick = removeSubstr(u.Nick, u.Callsign)
	}
	if options.MiscChanges {
		if strings.HasSuffix(u.City, " (B,") {
			length := len(u.City) - len(" (B,")
			u.City = u.City[:length]
		}
	}
	if options.FixRomanNumerals {
		u.Name = fixRomanNumerals(u.Name)
	}

	u.normalize()
}

func (db *UsersDB) amendUsers() {
	for _, u := range db.users {
		u.amend(db.options)
	}
}

func (u *User) normalize() {
	u.Callsign = normalizeString(u.Callsign)
	u.Name = normalizeString(u.Name)
	u.City = normalizeString(u.City)
	u.State = normalizeString(u.State)
	u.Nick = normalizeString(u.Nick)
	u.Country = normalizeString(u.Country)
}

func normalizeString(field string) string {
	field = asciify(field)
	field = strings.TrimSpace(field)
	field = strings.Replace(field, ",", ";", -1)

	for strings.Index(field, "  ") >= 0 {
		field = strings.Replace(field, "  ", " ", -1)
	}

	return field
}

func asciify(field string) string {
	runes := []rune(field)
	strs := make([]string, len(runes))
	for i, r := range runes {
		strs[i] = transliterations[r]
	}

	return strings.Join(strs, "")
}

func (u *User) fixCallsigns() {
	if u.ID < 1000000 {
		return
	}
	u.Callsign = strings.Replace(u.Callsign, " ", "", -1)
	u.Callsign = strings.Replace(u.Callsign, ".", "", -1)
}

func abbreviateDirections(field string) string {
	words := strings.Split(field, " ")
	dir, ok := directionAbbreviations[words[0]]
	if ok {
		words[0] = dir
	}
	return strings.Join(words, " ")
}

func removeDupSurnames(field string) string {
	words := strings.Split(field, " ")
	length := len(words)
	if length < 3 || words[length-2] != words[length-1] {
		return field
	}

	return strings.Join(words[:length-1], " ")
}

func removeRepeats(field string) string {
	words := strings.Split(field, " ")
	if len(words) < 4 || len(words)%2 != 0 {
		return field
	}

	halfLen := len(words) / 2
	for i := 0; i < halfLen; i++ {
		if words[i] != words[i+halfLen] {
			return field
		}
	}
	return strings.Join(words[:halfLen], " ")
}

func titleCase(field string) string {
	words := strings.Split(field, " ")
	for i, word := range words {
		title := titleCaseMap[word]
		if title != "" {
			words[i] = title
		}
	}

	return strings.Join(words, " ")
}

func checkTitleCase(users []*User) {
	upperCaseMap := make(map[string]bool)
	for _, word := range upperCaseWords {
		upperCaseMap[word] = true
	}

	fmt.Println("new upper-case words:")
	for _, u := range users {
		fields := []string{
			u.Name,
			u.City,
			u.State,
			u.Nick,
			u.Country,
		}
		for _, field := range fields {
		nextWord:
			for _, word := range strings.Split(field, " ") {
				if len(word) < 2 {
					continue
				}

				for r := range word {
					if r < 'A' || r > 'Z' {
						continue nextWord
					}
				}

				if titleCaseMap[word] != "" {
					continue
				}

				if upperCaseMap[word] {
					continue
				}

				fmt.Println(word)
			}
		}
	}

	fmt.Println("end of new upper-case words")
}

func (u *User) removeMatchingNicks() {
	firstName := strings.SplitN(u.Name, " ", 2)[0]
	if u.Nick == firstName {
		u.Nick = ""
	}
}

func (u *User) addNicks() {
	firstName := strings.SplitN(u.Name, " ", 2)[0]
	if u.Nick == "" {
		u.Nick = firstName
	}
}

func removeSubstr(field string, subf string) string {
	index := strings.Index(strings.ToUpper(field), strings.ToUpper(subf))
	if index >= 0 {
		field = field[:index] + field[index+len(subf):]
	}

	return field
}

func fixRomanNumerals(field string) string {
	fLen := len(field)
	if fLen < 3 {
		return field
	}

	if strings.HasSuffix(field, "i") {
		if strings.HasSuffix(field, " Ii") {
			field = field[:fLen-1] + "I"
		} else if strings.HasSuffix(field, " Iii") {
			field = field[:fLen-2] + "II"
		}
	} else if strings.HasSuffix(field, " Iv") {
		field = field[:fLen-1] + "V"
	}

	return field
}

func (u *User) usCallsign() bool {
	runes := []rune(u.Callsign)
	if strings.ContainsRune("KNW", runes[0]) {
		return true
	}

	if runes[0] == 'A' && runes[1] >= 'A' && runes[1] <= 'L' {
		return true
	}

	return false
}

func (u *User) fixStateCountries() {
	for country, stateAbbrevs := range stateAbbreviationsByCountry {
		for state := range stateAbbrevs {
			if u.Country == state {
				if state == "Georgia" && !u.usCallsign() {
					continue
				}
				if u.State == "" {
					u.State = state
				}
				u.Country = country
			}
		}
	}
}

func downloadURLBytes(url string) ([]byte, error) {
	resp, err := client.Get(url)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != 200 {
		return nil, errors.New(resp.Status)
	}

	return ioutil.ReadAll(resp.Body)
}

func downloadURLLines(url string) ([]string, error) {
	bytes, err := downloadURLBytes(url)
	if err != nil {
		return nil, err
	}

	lines := strings.Split(string(bytes), "\n")

	return lines[:len(lines)-1], nil
}

type RadioidTop struct {
	RadioidUsers []*RadioidUser `json:"users"`
}

type RadioidUser struct {
	ID       int    `json:"radio_id"`
	Callsign string `json:"callsign"`
	Name     string `json:"name"`
	Surname  string `json:"surname"`
	City     string `json:"city"`
	State    string `json:"state"`
	Country  string `json:"country"`
}

func downloadRadioidUsers() ([]*User, error) {
	bytes, err := downloadURLBytes(radioidUsersURL)
	if err != nil {
		return nil, err
	}

	var top RadioidTop
	err = json.Unmarshal(bytes, &top)
	if err != nil {
		errFmt := "error downloading radioid users database: %s: %s"
		err = fmt.Errorf(errFmt, radioidUsersURL, err.Error())
		return nil, err
	}

	if len(top.RadioidUsers) < 50000 {
		errFmt := "too few radioid users database entries: %s: %d"
		err = fmt.Errorf(errFmt, radioidUsersURL, len(top.RadioidUsers))
		return nil, err
	}

	users := make([]*User, 0)
	for _, ru := range top.RadioidUsers {
		if ru.Callsign == "RADIOID" {
			continue
		}

		u := &User{
			ID:       ru.ID,
			Callsign: ru.Callsign,
			Name:     ru.Name + " " + ru.Surname,
			City:     ru.City,
			State:    ru.State,
			Country:  ru.Country,
		}

		users = append(users, u)
	}
	return users, nil
}

func stringToID(s string) (int, error) {
	s = strings.TrimPrefix(s, "#")
	if s == "" {
		return 0, nil
	}
	id64, err := strconv.ParseUint(s, 10, 24)
	if err != nil {
		return 0, err
	}
	return int(id64), nil
}

func downloadCuratedUsers() ([]*User, error) {
	lines, err := downloadURLLines(curatedUsersURL)
	if err != nil {
		return nil, err
	}

	users := make([]*User, len(lines))
	for i, line := range lines {
		fields := strings.Split(line, ",")
		if len(fields) < 7 {
			continue
		}
		id, err := stringToID(fields[0])
		if err != nil {
			return nil, err
		}
		users[i] = &User{
			ID:       id,
			Callsign: fields[1],
			Name:     fields[2],
			City:     fields[3],
			State:    fields[4],
			Nick:     fields[5],
			Country:  fields[6],
		}
	}
	return users, nil
}

func linesToUsers(url string, lines []string) ([]*User, error) {
	users := make([]*User, 0, len(lines))
	errStrs := make([]string, 0)
	for i, line := range lines {
		fmtStr := ""
		fields := strings.Split(line, ",")
		id, err := strconv.ParseInt(fields[0], 10, 64)
		if err != nil || id > 16777215 {
			fmtStr = "%s%d invalid DMR ID value: %s"
			if err != nil {
				fmtStr = "%s:%d non-numeric DMR ID: %s"
			}
			err := fmt.Sprintf(fmtStr, url, i, line)
			errStrs = append(errStrs, err)
			continue
		}
		if len(fields) != 7 {
			if i == 0 {
				continue
			}
			fmtStr := "%s:%d too many fields: %s"
			if len(fields) < 7 {
				fields = append(fields, []string{
					"", "", "", "", "", "", "",
				}...)
				fmtStr = "%s:%d too few fields: %s"
			}
			err := fmt.Sprintf(fmtStr, url, i, line)
			errStrs = append(errStrs, err)
			fields = fields[:7]
		}
		user := &User{
			ID:       int(id),
			Callsign: fields[1],
			Name:     fields[2],
			City:     fields[3],
			State:    fields[4],
			Nick:     fields[5],
			Country:  fields[6],
		}
		users = append(users, user)
	}

	err := errors.New(strings.Join(errStrs, "\n"))
	if len(errStrs) == 0 {
		err = nil
	}

	return users, err
}

func readFileUsersFuncs(path string) []func() ([]*User, error) {
	funcs := make([]func() ([]*User, error), 1)
	funcs[0] = func() ([]*User, error) {
		file, err := os.Open(path)
		if err != nil {
			return nil, err
		}
		defer file.Close()

		lines := make([]string, 0)
		scanner := bufio.NewScanner(file)
		for scanner.Scan() {
			lines = append(lines, scanner.Text())
		}

		err = scanner.Err()
		if err != nil {
			return nil, err
		}
		return linesToUsers(path, lines)
	}
	return funcs
}

func newURLUsersFuncs(uri string) []func() ([]*User, error) {
	funcs := make([]func() ([]*User, error), 1)
	funcs[0] = func() ([]*User, error) {
		lines, err := downloadURLLines(uri)
		if err != nil {
			return nil, err
		}

		return linesToUsers(uri, lines)
	}
	return funcs
}

func downloadFixedUsers() ([]*User, error) {
	lines, err := downloadURLLines(fixedUsersURL)
	if err != nil {
		errFmt := "downloading fixed users: %s: %s"
		err = fmt.Errorf(errFmt, fixedUsersURL, err.Error())
		return nil, err
	}

	users := make([]*User, len(lines))
	for i, line := range lines {
		fields := strings.Split(line, ",")
		if len(fields) < 2 {
			continue
		}
		id, err := stringToID(fields[0])
		if err != nil {
			return nil, err
		}
		users[i] = &User{
			ID:       id,
			Callsign: fields[1],
		}
	}
	return users, nil
}

func downloadpd1wpUsers() ([]*User, error) {
	lines, err := downloadURLLines(pd1wpUsersURL)
	if err != nil {
		errFmt := "downloading pd1wp users: %s: %s"
		err = fmt.Errorf(errFmt, pd1wpUsersURL, err.Error())
		return nil, err
	}

	users := make([]*User, len(lines))
	for i, line := range lines {
		fields := strings.Split(line, ",")
		if len(fields) < 7 {
			continue
		}
		id, err := stringToID(fields[0])
		if err != nil {
			return nil, err
		}
		users[i] = &User{
			ID:       id,
			Callsign: fields[1],
			Name:     fields[2],
			City:     fields[3],
			State:    fields[4],
			Nick:     fields[5],
			Country:  fields[6],
		}
	}
	return users, nil
}

func downloadpd1wpUsersNames() ([]*User, error) {
	lines, err := downloadURLLines(pd1wpUsersURL)
	if err != nil {
		errFmt := "downloading pd1wp users: %s: %s"
		err = fmt.Errorf(errFmt, pd1wpUsersURL, err.Error())
		return nil, err
	}

	users := make([]*User, len(lines))
	for i, line := range lines {
		fields := strings.Split(line, ",")
		if len(fields) < 7 {
			continue
		}
		id, err := stringToID(fields[0])
		if err != nil {
			return nil, err
		}
		users[i] = &User{
			ID:   id,
			Name: fields[2],
			Nick: fields[5],
		}
	}
	return users, nil
}

func downloadOverrideUsers() ([]*User, error) {
	lines, err := downloadURLLines(overrideUsersURL)
	if err != nil {
		errFmt := "downloading override users: %s: %s"
		err = fmt.Errorf(errFmt, overrideUsersURL, err.Error())
		return nil, err
	}

	users := make([]*User, len(lines))
	for i, line := range lines {
		fields := strings.Split(line, ",")
		if len(fields) < 7 {
			continue
		}
		id, err := stringToID(fields[0])
		if err != nil {
			return nil, err
		}
		users[i] = &User{
			ID:       id,
			Callsign: fields[1],
			Name:     fields[2],
			City:     fields[3],
			State:    fields[4],
			Nick:     fields[5],
			Country:  fields[6],
		}
	}
	return users, nil
}

type special struct {
	ID      string
	Country string
	Address string
}

func downloadSpecialURLs() ([]string, error) {
	bytes, err := downloadURLBytes(specialUsersURL)
	if err != nil {
		return nil, err
	}

	var specials []special
	err = json.Unmarshal(bytes, &specials)

	var urls []string
	for _, s := range specials {
		url := "http://" + s.Address + "/md380tools/special_IDs.csv"
		urls = append(urls, url)
	}

	return urls, nil
}

func downloadSpecialUsers(url string) ([]*User, error) {
	lines, err := downloadURLLines(url)
	if err != nil {
		errFmt := "downloading special users: %s: %s"
		err = fmt.Errorf(errFmt, url, err.Error())
		return nil, nil // Ignore erros on special users
	}

	users := make([]*User, len(lines))
	for i, line := range lines {
		fields := strings.Split(line, ",")
		if len(fields) < 7 {
			continue
		}
		id, err := stringToID(fields[0])
		if err != nil {
			return nil, err
		}
		users[i] = &User{
			ID:       id,
			Callsign: fields[1],
			Name:     fields[2],
			Country:  fields[6],
		}
	}
	return users, nil
}

func downloadReflectorUsers() ([]*User, error) {
	lines, err := downloadURLLines(reflectorUsersURL)
	if err != nil {
		errFmt := "downloading reflector users: %s: %s"
		err = fmt.Errorf(errFmt, reflectorUsersURL, err.Error())
		return nil, err
	}

	users := make([]*User, len(lines))
	for i, line := range lines[1:] {
		line := strings.Replace(line, "@", ",", 2)
		fields := strings.Split(line, ",")
		if len(fields) < 2 {
			continue
		}
		id, err := stringToID(fields[0])
		if err != nil {
			return nil, err
		}
		users[i] = &User{
			ID:       id,
			Callsign: fields[1],
		}
	}
	return users, nil
}

func (db *UsersDB) mergeAndSortUsers() {
	idMap := make(map[int]*User)
	for _, u := range db.users {
		if u == nil || u.ID == 0 {
			continue
		}
		id := u.ID
		existing := idMap[id]
		if existing == nil {
			idMap[int(id)] = u
			continue
		}
		// non-empty fields in later entries replace fields in earlier
		if u.Callsign != "" {
			existing.Callsign = u.Callsign
		}
		if u.Name != "" {
			existing.Name = u.Name
		}
		if u.City != "" {
			existing.City = u.City
		}
		if u.State != "" {
			existing.State = u.State
		}
		if u.Nick != "" {
			existing.Nick = u.Nick
		}
		if u.Country != "" {
			existing.Country = u.Country
		}
		idMap[id] = existing
	}

	ids := make([]int, 0, len(idMap))
	for id := range idMap {
		ids = append(ids, id)
	}

	users := make([]*User, len(ids))
	sort.Ints(ids)
	for i, id := range ids {
		users[i] = idMap[id]
	}

	db.users = users
}

type result struct {
	index int
	users []*User
	err   error
}

func do(index int, f func() ([]*User, error), resultChan chan result) {
	var r result

	r.index = index
	r.users, r.err = f()
	resultChan <- r
}

// getUsers - Return the best current list of DMR users
func (db *UsersDB) getUsers() error {
	resultCount := len(db.getUsersFuncs)
	resultChan := make(chan result, resultCount)

	for i, f := range db.getUsersFuncs {
		go do(i, f, resultChan)
	}

	db.setMaxProgressCount(resultCount)

	results := make([]result, resultCount)
	for done := 0; done < resultCount; {
		select {
		case r := <-resultChan:
			if r.err != nil {
				return r.err
			}
			results[r.index] = r
			done++
			err := db.progressFunc()
			if err != nil {
				return err
			}
		}
	}
	for _, r := range results {
		db.users = append(db.users, r.users...)
	}

	db.mergeAndSortUsers()

	db.finalProgress()
	return nil
}

// Users - Return the, possibly filtered, current list of DMR users
func (db *UsersDB) Users() []*User {
	db.amendUsers()

	if !db.options.FilterByCountries {
		return db.users
	}

	users := make([]*User, 0)
	for _, user := range db.users {
		if db.IncludedCountries[user.fullCountry] {
			users = append(users, user)
		}
	}
	return users
}

func (db *UsersDB) MD380String() string {
	users := db.Users()
	strs := make([]string, len(users))
	for i, u := range users {
		strs[i] = fmt.Sprintf("%d,%s,%s,%s,%s,%s,%s",
			u.ID, u.Callsign, u.Name, u.City, u.State, u.Nick, u.Country)
	}
	strs[len(strs)-1] += "\n"
	return strings.Join(strs, "\n")
}

func (db *UsersDB) UV380Image() []byte {
	users := db.Users()

	if len(users) > MaxUV380Users {
		users = users[:MaxUV380Users]
	}
	nUsers := len(users)

	image := bytes.Repeat([]byte{0xff}, 0x1000000-0x200000)

	image[0] = byte(nUsers >> 16)
	image[1] = byte(nUsers >> 8)
	image[2] = byte(nUsers)

	lastHigh12 := -1
	j := 0
	for i, u := range users {
		high12 := u.ID >> 12
		if high12 == lastHigh12 {
			continue
		}
		offset := 3 + j*4
		index := i + 1
		image[offset] = byte(u.ID >> 16)
		image[offset+1] = byte(((u.ID >> 8) & 0xf0) | (index >> 16))
		image[offset+2] = byte(index >> 8)
		image[offset+3] = byte(index)
		lastHigh12 = high12
		j++
	}

	for i, u := range users {
		userOffset := 0x4003 + i*120

		idOffset := userOffset
		callOffset := userOffset + 4
		restOffset := userOffset + 20

		image[idOffset] = byte(u.ID)
		image[idOffset+1] = byte(u.ID >> 8)
		image[idOffset+2] = byte(u.ID >> 16)

		zeros := bytes.Repeat([]byte{0}, 116)
		copy(image[callOffset:callOffset+116], zeros)

		copy(image[callOffset:callOffset+15], u.Callsign)

		restFields := []string{
			u.Name,
			u.Nick,
			u.City,
			u.State,
			u.Country,
		}
		rest := strings.Join(restFields, ",")
		copy(image[restOffset:restOffset+99], rest)
	}

	// truncate image to 1KB boundary
	end := (0x4003 + len(users)*120 + 1023) & ^1023

	return image[:end]
}

func (db *UsersDB) AllCountries() ([]string, error) {
	allUsers := db.Users()
	if len(db.users) == 0 {
		var err error
		err = db.getUsers()
		if err != nil {
			return nil, err
		}
		allUsers = db.users
	}

	countriesMap := make(map[string]bool)
	for _, user := range allUsers {
		countriesMap[user.fullCountry] = true
	}
	countries := make([]string, 0)
	for country := range countriesMap {
		countries = append(countries, country)
	}

	sort.Strings(countries)

	return countries, nil
}

func (db *UsersDB) IncludeCountries(countries ...string) {
	db.IncludedCountries = make(map[string]bool)
	for _, country := range countries {
		db.IncludedCountries[country] = true
	}
}

func mergeUser(existing, u *User) *User {
	if u.Callsign != "" {
		existing.Callsign = u.Callsign
	}
	if u.Name != "" {
		existing.Name = u.Name
	}
	if u.City != "" {
		existing.City = u.City
	}
	if u.State != "" {
		existing.State = u.State
	}
	if u.Nick != "" {
		existing.Nick = u.Nick
	}
	if u.Country != "" {
		existing.Country = u.Country
	}

	return existing
}

func (db *UsersDB) writeWithHeader() (err error) {
	file, err := os.Create(db.filename)
	if err != nil {
		return err
	}
	defer func() {
		fErr := file.Close()
		if err == nil {
			err = fErr
		}
		return
	}()

	fmt.Fprintln(file, "Radio ID,CallSign,Name,City,State,Firstname,Country")
	_, err = file.WriteString(db.MD380String())
	if err != nil {
		return err
	}

	return nil
}

// WriteMD380ToolsFile - Write a user db file in MD380 format
func (db *UsersDB) WriteMD380ToolsFile(filename string) error {
	file, err := os.Create(filename)
	if err != nil {
		return err
	}
	defer func() {
		fErr := file.Close()
		if err == nil {
			err = fErr
		}
		return
	}()

	str := db.MD380String()

	fmt.Fprintf(file, "%d\n", len(str))

	_, err = file.WriteString(str)
	if err != nil {
		return err
	}

	return nil
}
