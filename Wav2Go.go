package main

import (
	"bytes"

	//"crypto/dsa" //depreciated
	"crypto/ecdsa"
	"crypto/elliptic"

	//"crypto/aes"
	//"crypto/des"
	//"crypto/ed25519"
	"crypto/md5"
	"crypto/rand"

	//"hash"
	//"crypto/rsa"
	//"crypto"
	//"crypto/cipher"
	"crypto/tls"
	//_ "crypto/tls/fipsonly"
	"crypto/x509"
	"crypto/x509/pkix"

	//"encoding/asn1"

	"encoding/binary"
	"encoding/hex"
	"encoding/pem"
	"errors"
	"fmt"
	"io"
	"log"
	"math"
	"math/big"
	"math/cmplx"
	rand2 "math/rand"
	"net"
	"os"
	"runtime"
	"strconv"
	"strings"
	"time"

	// "pkg.go.dev/golang.org/x/exp" //mmap waiting...experimental.

	ffmpeg "github.com/u2takey/ffmpeg-go"
)

///// CREDITS ----> github.com/DylanMeeus/GoAudio/

func generate(datafile string, reqFrames int64, wfmt WaveFmt) ([]float64, []float64) {
	MinFloat64 := 2.2 * math.Pow10(-308)
	frames := make([]float64, reqFrames)
	var OutOfBoundsFrames []float64
	//osc, err := NewOscillator(wfmt.SampleRate, shape)
	//if err != nil {
	//	panic(err)
	//}
	//rand.Seed(time.Now().Unix())
	//var data2 [][]byte
	data, err := ReadDataFile(datafile)
	if err != nil {
		panic(err)
	}

	size := wfmt.BitsPerSample / 8 //32 = 4
	var FrameSamples [][]byte
	for i := 0; i < len(data); i = i + size {
		FrameSamples = append(FrameSamples, data[i:i+size])
	}
	j := 0
	for i := range frames {
		if i >= len(FrameSamples) {
			frames[i] = MinFloat64 //hexadecimal representation = NULL BYTES PADDING
		} else {
			frame := bitsToFloat(FrameSamples[j]) * math.Pow10(307) * math.Pow10(1)
			if frame >= MinFloat64 && frame <= math.MaxFloat64 {
				frames[i] = frame
			} else {
				frames[i] = 0
				OutOfBoundsFrames = append(OutOfBoundsFrames, frame)
			}
			//fmt.Println(frames[i])
			//data2 = append(data2, floatToBytes(float64(frames[i]), size))
			j++
		}
	}
	return frames, OutOfBoundsFrames
}

// Breakpoints is a collection of Breakpoint (time:value) pairs
type Breakpoints []Breakpoint

// Breakpoint represents a time:value pair
type Breakpoint struct {
	Time, Value float64
}

// BreakpointStream can be used to to treat breakpoints as a stream of data
// Each 'tick' can manipulate the state of the breakpoint stream
type BreakpointStream struct {
	Breakpoints     Breakpoints
	Left            Breakpoint
	Right           Breakpoint
	IndexLeft       int
	IndexRight      int
	CurrentPosition float64 // current position in timeframes
	Increment       float64
	Width           float64
	Height          float64
	HasMore         bool
}

// Tick returns the next value in the breakpoint stream
func (b *BreakpointStream) Tick() (out float64) {
	//if !b.HasMore {
	// permanently the last value
	//	return b.Right.Value
	//}
	if b.Width == 0.0 {
		out = b.Right.Value
	} else {
		// figure out value from linear interpolation
		frac := (float64(b.CurrentPosition) - b.Left.Time) / b.Width
		out = b.Left.Value + (b.Height * frac)
	}

	// prepare for next frame
	b.CurrentPosition += b.Increment
	if b.CurrentPosition > b.Right.Time {
		// move to next span
		b.IndexLeft++
		b.IndexRight++
		if b.IndexRight < len(b.Breakpoints) {
			b.Left = b.Breakpoints[b.IndexLeft]
			b.Right = b.Breakpoints[b.IndexRight]
			b.Width = b.Right.Time - b.Left.Time
			b.Height = b.Right.Value - b.Left.Value
		} else {
			// no more points
			b.HasMore = false
		}
	}
	return out
}

// NewBreakpointStream represents a slice of breakpoints streamed at a given sample rate
func NewBreakpointStream(bs []Breakpoint, sr int) (*BreakpointStream, error) {
	if len(bs) == 0 {
		return nil, errors.New("Need at least two points to create a stream")
	}
	left, right := bs[0], bs[1]
	return &BreakpointStream{
		Breakpoints:     Breakpoints(bs),
		Increment:       1.0 / float64(sr),
		IndexLeft:       0,
		IndexRight:      1,
		CurrentPosition: 0,
		Left:            left,
		Right:           right,
		Width:           right.Time - left.Time,   // first span
		Height:          right.Value - left.Value, // diff of first span
		HasMore:         len(bs) > 0,
	}, nil
}

// ParseBreakpoints reads the breakpoints from an io.Reader
// and turns them into a slice.
// A file is expected to be [time: value] formatted
// Will panic if file format is wrong
// TODO: don't panic
func ParseBreakpoints(in io.Reader) ([]Breakpoint, error) {
	data, err := io.ReadAll(in)
	if err != nil {
		return nil, err
	}

	lines := strings.Split(string(data), "\n")

	brkpnts := []Breakpoint{}
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		parts := strings.Split(line, ":")
		if len(parts) != 2 {
			return brkpnts, err
		}
		time := parts[0]
		value := parts[1]

		tf, err := strconv.ParseFloat(time, 64)
		if err != nil {
			return brkpnts, err
		}
		vf, err := strconv.ParseFloat(value, 64)
		if err != nil {
			return brkpnts, err
		}

		brkpnts = append(brkpnts, Breakpoint{
			Time:  tf,
			Value: vf,
		})

	}
	return brkpnts, nil
}

// ValueAt returns the expected value at a given time (expressed as float64) by linear interpolation
// Returns the index at which we found our value as well as the value itself.
func ValueAt(bs []Breakpoint, time float64, startIndex int) (index int, value float64) {
	if len(bs) == 0 {
		return 0, 0
	}
	npoints := len(bs)

	// first we need to find a span containing our timeslot
	startSpan := startIndex // start of span
	for _, b := range bs[startSpan:] {
		if b.Time > time {
			break
		}
		startSpan++
	}

	// Our span is never-ending (the last point in our breakpoint file was hit)
	if startSpan == npoints {
		return startSpan, bs[startSpan-1].Value
	}

	left := bs[startSpan-1]
	right := bs[startSpan]

	// check for instant jump
	// 2 points having the same time...
	width := right.Time - left.Time

	if width == 0 {
		return startSpan, right.Value
	}

	frac := (time - left.Time) / width

	val := left.Value + ((right.Value - left.Value) * frac)

	return startSpan, val
}

// MinMaxValue returns the smallest and largest value found in the breakpoint file
func MinMaxValue(bs []Breakpoint) (smallest float64, largest float64) {
	// TODO: implement as SORT and return the first and last element
	if len(bs) == 0 {
		return
	}
	smallest = bs[0].Value
	largest = bs[0].Value
	for _, b := range bs[1:] {
		if b.Value < smallest {
			smallest = b.Value
		} else if b.Value > largest {
			largest = b.Value
		} else {
			// no op
		}
	}
	return
}

// Any returns true if any breakpoint matches the filter.
func (bs Breakpoints) Any(f func(Breakpoint) bool) bool {
	for _, b := range bs {
		if f(b) {
			return true
		}
	}
	return false
}

// DFT is a discrete fourier transformation on the input frames
// DEPRECATED
// Please use FFT unless you are sure  you want this one..
func DFT(input []Frame) []complex128 {
	N := len(input)

	output := make([]complex128, len(input))

	reals := make([]float64, len(input))
	imgs := make([]float64, len(input))
	for i, frame := range input {
		for n := 0; n < N; n++ {
			reals[i] += float64(frame) * math.Cos(float64(i*n)*tau/float64(N))
			imgs[i] += float64(frame) * math.Sin(float64(i*n)*tau/float64(N))
		}

		reals[i] /= float64(N)
		imgs[i] /= float64(N)
	}

	for i := 0; i < len(reals); i++ {
		output[i] = complex(reals[i], imgs[i])
	}

	return output
}

// HFFT mutates freqs!
func HFFT(input []Frame, freqs []complex128, n, step int) {
	if n == 1 {
		freqs[0] = complex(input[0], 0)
		return
	}

	h := n / 2

	HFFT(input, freqs, h, 2*step)
	HFFT(input[step:], freqs[h:], h, 2*step)

	for k := 0; k < h; k++ {
		a := -2 * math.Pi * float64(k) * float64(n)
		e := cmplx.Rect(1, a) * freqs[k+h]
		freqs[k], freqs[k+h] = freqs[k]+e, freqs[k]-e
	}
}

// FFT (Fast Fourier Transform) implementation
func FFT(input []Frame) []complex128 {
	freqs := make([]complex128, len(input))
	HFFT(input, freqs, len(input), 1)
	return freqs
}

// EqualTemperedNote
type EqualTemperedNote float64

// These constants represent the frequncies for the equal-tempered scale tuned to A4 = 440Hz
const (
	C0  EqualTemperedNote = 16.35
	C0S EqualTemperedNote = 17.32
	D0  EqualTemperedNote = 18.35
	D0S EqualTemperedNote = 19.45
	E0  EqualTemperedNote = 20.60
	F0  EqualTemperedNote = 21.83
	F0S EqualTemperedNote = 23.12
	G0  EqualTemperedNote = 24.50
	G0S EqualTemperedNote = 25.96
	A0  EqualTemperedNote = 27.50
	A0S EqualTemperedNote = 29.14
	B0  EqualTemperedNote = 30.87
	C1  EqualTemperedNote = 32.70
	C1S EqualTemperedNote = 34.65
	D1  EqualTemperedNote = 36.71
	D1S EqualTemperedNote = 38.89
	E1  EqualTemperedNote = 41.20
	F1  EqualTemperedNote = 43.65
	F1S EqualTemperedNote = 46.25
	G1  EqualTemperedNote = 49.00
	G1S EqualTemperedNote = 51.91
	A1  EqualTemperedNote = 55.00
	A1S EqualTemperedNote = 58.27
	B1  EqualTemperedNote = 61.74
	C2  EqualTemperedNote = 65.41
	C2S EqualTemperedNote = 69.30
	D2  EqualTemperedNote = 73.42
	D2S EqualTemperedNote = 77.78
	E2  EqualTemperedNote = 82.41
	F2  EqualTemperedNote = 87.31
	F2S EqualTemperedNote = 92.50
	G2  EqualTemperedNote = 98.00
	G2S EqualTemperedNote = 103.83
	A2  EqualTemperedNote = 110.00
	A2S EqualTemperedNote = 116.54
	B2  EqualTemperedNote = 123.47
	C3  EqualTemperedNote = 130.81
	C3S EqualTemperedNote = 138.59
	D3  EqualTemperedNote = 146.83
	D3S EqualTemperedNote = 155.56
	E3  EqualTemperedNote = 164.81
	F3  EqualTemperedNote = 174.61
	F3S EqualTemperedNote = 185.00
	G3  EqualTemperedNote = 196.00
	G3S EqualTemperedNote = 207.65
	A3  EqualTemperedNote = 220.00
	A3S EqualTemperedNote = 233.08
	B3  EqualTemperedNote = 246.94
	C4  EqualTemperedNote = 261.63
	C4S EqualTemperedNote = 277.18
	D4  EqualTemperedNote = 293.66
	D4S EqualTemperedNote = 311.13
	E4  EqualTemperedNote = 329.63
	F4  EqualTemperedNote = 349.23
	F4S EqualTemperedNote = 369.99
	G4  EqualTemperedNote = 392.00
	G4S EqualTemperedNote = 415.30
	A4  EqualTemperedNote = 440.00
	A4S EqualTemperedNote = 466.16
	B4  EqualTemperedNote = 493.88
	C5  EqualTemperedNote = 523.25
	C5S EqualTemperedNote = 554.37
	D5  EqualTemperedNote = 587.33
	D5S EqualTemperedNote = 622.25
	E5  EqualTemperedNote = 659.25
	F5  EqualTemperedNote = 698.46
	F5S EqualTemperedNote = 739.99
	G5  EqualTemperedNote = 783.99
	G5S EqualTemperedNote = 830.61
	A5  EqualTemperedNote = 880.00
	A5S EqualTemperedNote = 932.33
	B5  EqualTemperedNote = 987.77
	C6  EqualTemperedNote = 1046.50
	C6S EqualTemperedNote = 1108.73
	D6  EqualTemperedNote = 1174.66
	D6S EqualTemperedNote = 1244.51
	E6  EqualTemperedNote = 1318.51
	F6  EqualTemperedNote = 1396.91
	F6S EqualTemperedNote = 1479.98
	G6  EqualTemperedNote = 1567.98
	G6S EqualTemperedNote = 1661.22
	A6  EqualTemperedNote = 1760.00
	A6S EqualTemperedNote = 1864.66
	B6  EqualTemperedNote = 1975.53
	C7  EqualTemperedNote = 2093.00
	C7S EqualTemperedNote = 2217.46
	D7  EqualTemperedNote = 2349.32
	D7S EqualTemperedNote = 2489.02
	E7  EqualTemperedNote = 2636.02
	F7  EqualTemperedNote = 2793.83
	F7S EqualTemperedNote = 2959.96
	G7  EqualTemperedNote = 3135.96
	G7S EqualTemperedNote = 3322.44
	A7  EqualTemperedNote = 3520.00
	A7S EqualTemperedNote = 3729.31
	B7  EqualTemperedNote = 3951.07
	C8  EqualTemperedNote = 4186.01
	C8S EqualTemperedNote = 4434.92
	D8  EqualTemperedNote = 4698.63
	D8S EqualTemperedNote = 4978.03
	E8  EqualTemperedNote = 5274.04
	F8  EqualTemperedNote = 5587.65
	F8S EqualTemperedNote = 5919.91
	G8  EqualTemperedNote = 6271.93
	G8S EqualTemperedNote = 6644.88
	A8  EqualTemperedNote = 7040.00
	A8S EqualTemperedNote = 7458.62
	B8  EqualTemperedNote = 7902.13
)

// Lowpass applies a low-pass filter to the frames
// Does not modify the input signal
func Lowpass(fs []float64, freq, delay, sr float64) []float64 {
	output := make([]float64, len(fs))
	copy(output, fs)

	costh := 2. - math.Cos((tau*freq)/sr)
	coef := math.Sqrt(costh*costh-1.) - costh

	for i, a := range output {
		output[i] = a*(1+coef) - delay*coef
		delay = output[i]
	}

	return output
}

// Highpass applies a high-pass filter to the frames.
// Does not modify the input signal
func Highpass(fs []float64, freq, delay, sr float64) []float64 {
	output := make([]float64, len(fs))
	copy(output, fs)

	b := 2. - math.Cos(tau*freq/sr)
	coef := b - math.Sqrt(b*b-1.)

	for i, a := range output {
		output[i] = a*(1.-coef) - delay*coef
		delay = output[i]
	}

	return output
}

// Balance a signal (rescale output signal)
func Balance(signal, comparator, delay []float64, frequency, samplerate float64) []float64 {
	c := make([]float64, len(signal))
	copy(signal, c)

	costh := 2. - math.Cos(tau*frequency/samplerate)
	coef := math.Sqrt(costh*costh-1.) - costh

	for i, s := range signal {
		ss := signal[i]
		if signal[i] < 0 {
			ss = -s
		}
		delay[0] = ss*(1+coef) - (delay[0] * coef)

		if comparator[i] < 0 {
			comparator[i] = -comparator[i]
		}
		delay[1] = comparator[i]*(1+coef) - (delay[1] * coef)
		if delay[0] != 0 {
			c[i] = s * (delay[0] / delay[1])
		} else {
			c[i] = s * delay[1]
		}
	}
	return c
}

// Gtable is a Guard-table for oscillator lookup
type Gtable struct {
	data []float64
}

// Len returns the length of the data segment without the guard point
func Len(g *Gtable) int {
	return len(g.data) - 1
}

func NewGtable(data []float64) *Gtable {
	return &Gtable{data}
}

// NewSineTable returns a lookup table populated for sine-wave generation.
func NewSineTable(length int) *Gtable {
	g := &Gtable{}
	if length == 0 {
		return g
	}
	g.data = make([]float64, length+1) // one extra for the guard point.
	step := tau / float64(Len(g))
	for i := 0; i < Len(g); i++ {
		g.data[i] = math.Sin(step * float64(i))
	}
	// store a guard point
	g.data[len(g.data)-1] = g.data[0]
	return g
}

// NewTriangleTable generates a lookup table for a triangle wave
// of the specified length and with the requested number of harmonics.
func NewTriangleTable(length int, nharmonics int) (*Gtable, error) {
	if length == 0 || nharmonics == 0 || nharmonics >= length/2 {
		return nil, errors.New("invalid arguments for creation of Triangle Table")
	}

	g := &Gtable{}
	g.data = make([]float64, length+1)

	step := tau / float64(length)

	// generate triangle waveform
	harmonic := 1.0
	for i := 0; i < nharmonics; i++ {
		amp := 1.0 / (harmonic * harmonic)
		for j := 0; j < length; j++ {
			g.data[j] += amp * math.Cos(step*harmonic*float64(j))
		}
		harmonic += 2 // triangle wave has only odd harmonics
	}
	// normalize the values to be in the [-1;1] range
	g.data = normalize(g.data)
	return g, nil
}

// normalize the functions to the range -1, 1
func normalize(xs []float64) []float64 {
	length := len(xs)
	maxamp := 0.0
	for i := 0; i < length; i++ {
		amp := math.Abs(xs[i])
		if amp > maxamp {
			maxamp = amp
		}
	}

	maxamp = 1.0 / maxamp
	for i := 0; i < length; i++ {
		xs[i] *= maxamp
	}
	xs[len(xs)-1] = xs[0]
	return xs
}

// LookupOscillator is an oscillator that's more gentle on your CPU
// By performing a table lookup to generate the required waveform..
type LookupOscillator struct {
	Oscillator
	Table      *Gtable
	SizeOverSr float64 // convenience variable for calculations
}

// NewLookupOscillator creates a new oscillator which
// performs a table-lookup to generate the required waveform
func NewLookupOscillator(sr int, t *Gtable, phase float64) (*LookupOscillator, error) {
	if t == nil || len(t.data) == 0 {
		return nil, errors.New("invalid table provided for lookup oscillator")
	}

	return &LookupOscillator{
		Oscillator: Oscillator{
			curfreq:  0.0,
			curphase: float64(Len(t)) * phase,
			incr:     0.0,
		},
		Table:      t,
		SizeOverSr: float64(Len(t)) / float64(sr),
	}, nil

}

// TruncateTick performs a lookup and truncates the value
// index down (if the index for lookup = 10.5, return index 10)
func (l *LookupOscillator) TruncateTick(freq float64) float64 {
	return l.BatchTruncateTick(freq, 1)[0]
}

// BatchTruncateTick returns a slice of samples from the oscillator of the requested length
func (l *LookupOscillator) BatchTruncateTick(freq float64, nframes int) []float64 {
	out := make([]float64, nframes)
	for i := 0; i < nframes; i++ {
		index := l.curphase
		if l.curfreq != freq {
			l.curfreq = freq
			l.incr = l.SizeOverSr * l.curfreq
		}
		curphase := l.curphase
		curphase += l.incr
		for curphase > float64(Len(l.Table)) {
			curphase -= float64(Len(l.Table))
		}
		for curphase < 0.0 {
			curphase += float64(Len(l.Table))
		}
		l.curphase = curphase
		out[i] = l.Table.data[int(index)]
	}
	return out
}

// InterpolateTick performs a lookup but interpolates the value if the
// requested index does not appear in the table.
func (l *LookupOscillator) InterpolateTick(freq float64) float64 {
	return l.BatchInterpolateTick(freq, 1)[0]
}

// BatchInterpolateTick performs a lookup for N frames, and interpolates the value if the
// requested index does not appear in the table.
func (l *LookupOscillator) BatchInterpolateTick(freq float64, nframes int) []float64 {
	out := make([]float64, nframes)
	for i := 0; i < nframes; i++ {
		baseIndex := int(l.curphase)
		nextIndex := baseIndex + 1
		if l.curfreq != freq {
			l.curfreq = freq
			l.incr = l.SizeOverSr * l.curfreq
		}
		curphase := l.curphase
		frac := curphase - float64(baseIndex)
		val := l.Table.data[baseIndex]
		slope := l.Table.data[nextIndex] - val
		val += frac * slope
		curphase += l.incr

		for curphase > float64(Len(l.Table)) {
			curphase -= float64(Len(l.Table))
		}
		for curphase < 0.0 {
			curphase += float64(Len(l.Table))
		}

		l.curphase = curphase
		out[i] = val
	}
	return out
}

const tau = (2 * math.Pi)

// Shape for defining the different possible waveform shapes for use with the Oscillator
type Shape int

// Shapes for which we can generate waveforms
const (
	SINE Shape = iota
	SQUARE
	DOWNWARD_SAWTOOTH
	UPWARD_SAWTOOTH
	TRIANGLE
)

var (
	shapeCalcFunc = map[Shape]func(float64) float64{
		SINE:              sineCalc,
		SQUARE:            squareCalc,
		TRIANGLE:          triangleCalc,
		DOWNWARD_SAWTOOTH: downSawtoothCalc,
		UPWARD_SAWTOOTH:   upwSawtoothCalc,
	}
)

// Oscillator represents a wave-oscillator where each tick is calculated in the moment.
type Oscillator struct {
	curfreq  float64
	curphase float64
	incr     float64
	twopiosr float64 // (2*PI) / samplerate
	tickfunc func(float64) float64
}

// NewOscillator set to a given sample rate
func NewOscillator(sr int, shape Shape) (*Oscillator, error) {
	cf, ok := shapeCalcFunc[shape]
	if !ok {
		return nil, fmt.Errorf("Shape type %v not supported", shape)
	}
	return &Oscillator{
		twopiosr: tau / float64(sr),
		tickfunc: cf,
	}, nil
}

// NewPhaseOscillator creates a new oscillator where the initial phase is offset
// by a given phase
func NewPhaseOscillator(sr int, phase float64, shape Shape) (*Oscillator, error) {
	cf, ok := shapeCalcFunc[shape]
	if !ok {
		return nil, fmt.Errorf("Shape type %v not supported", shape)
	}
	return &Oscillator{
		twopiosr: tau / float64(sr),
		tickfunc: cf,
		curphase: tau * phase,
	}, nil
}

// Tick generates the next value of the oscillator waveform at a given frequency in Hz
func (o *Oscillator) Tick(freq float64) float64 {
	if o.curfreq != freq {
		o.curfreq = freq
		o.incr = o.twopiosr * freq
	}
	val := o.tickfunc(o.curphase)
	o.curphase += o.incr
	if o.curphase >= tau {
		o.curphase -= tau
	}
	if o.curphase < 0 {
		o.curphase = tau
	}
	return val

}

func triangleCalc(phase float64) float64 {
	val := 2.0*(phase*(1.0/tau)) - 1.0
	if val < 0.0 {
		val = -val
	}
	val = 2.0 * (val - 0.5)
	return val
}

func upwSawtoothCalc(phase float64) float64 {
	val := 2.0*(phase*(1.0/tau)) - 1.0
	return val
}

func downSawtoothCalc(phase float64) float64 {
	val := 1.0 - 2.0*(phase*(1.0/tau))
	return val
}

func squareCalc(phase float64) float64 {
	val := -1.0
	if phase <= math.Pi {
		val = 1.0
	}
	return val
}

func sineCalc(phase float64) float64 {
	return math.Sin(phase)
}

// type aliases for conversion functions
type (
	bytesToIntF   func([]byte) int
	bytesToFloatF func([]byte) float64
)

var (
	// figure out which 'to int' function to use..
	byteSizeToIntFunc = map[int]bytesToIntF{
		16: bits16ToInt,
		24: bits24ToInt,
		32: bits32ToInt,
	}

	byteSizeToFloatFunc = map[int]bytesToFloatF{
		16: bitsToFloat,
		32: bitsToFloat,
		64: bitsToFloat,
	}

	// max value depending on the bit size
	maxValues = map[int]int{
		8:  math.MaxInt8,
		16: math.MaxInt16,
		32: math.MaxInt32,
		64: math.MaxInt64,
	}
)

func ReadDataFile(f string) ([]byte, error) {
	// open as read-only file
	file, err := os.Open(f)
	if err != nil {
		return []byte{}, err
	}
	defer file.Close()

	return io.ReadAll(file)
}

// ReadWaveFile parses a .wave file into a Wave struct
func ReadWaveFile(f string) (Wave, error) {
	// open as read-only file
	file, err := os.Open(f)
	if err != nil {
		return Wave{}, err
	}
	defer file.Close()

	return ReadWaveFromReader(file)
}

// ReadWaveFromReader parses an io.Reader into a Wave struct
func ReadWaveFromReader(reader io.Reader) (Wave, error) {
	data, err := io.ReadAll(reader)
	if err != nil {
		return Wave{}, err
	}

	data = deleteJunk(data)

	hdr := readHeader(data)

	wfmt := readFmt(data)

	wavdata := readData(data, wfmt)

	frames := parseRawData(wfmt, wavdata.RawData)
	wavdata.Frames = frames

	return Wave{
		WaveHeader: hdr,
		WaveFmt:    wfmt,
		WaveData:   wavdata,
	}, nil
}

// for our wave format we expect double precision floats
func bitsToFloat(b []byte) float64 {
	var bits uint64
	switch len(b) {
	case 2:
		bits = uint64(binary.LittleEndian.Uint16(b))
	case 4:
		bits = uint64(binary.LittleEndian.Uint32(b))
	case 8:
		bits = binary.LittleEndian.Uint64(b)
	default:
		panic("Can't parse to float..")
	}
	float := math.Float64frombits(bits)
	return float
}

func bits16ToInt(b []byte) int {
	if len(b) != 2 {
		panic("Expected size 4!")
	}
	var payload int16
	buf := bytes.NewReader(b)
	err := binary.Read(buf, binary.LittleEndian, &payload)
	if err != nil {
		// TODO: make safe
		panic(err)
	}
	return int(payload) // easier to work with ints
}

func bits24ToInt(b []byte) int {
	if len(b) != 3 {
		panic("Expected size 3!")
	}
	// add some padding to turn a 24-bit integer into a 32-bit integer
	b = append([]byte{0x00}, b...)
	var payload int32
	buf := bytes.NewReader(b)
	err := binary.Read(buf, binary.LittleEndian, &payload)
	if err != nil {
		// TODO: make safe
		panic(err)
	}
	return int(payload) // easier to work with ints
}

// turn a 32-bit byte array into an int
func bits32ToInt(b []byte) int {
	if len(b) != 4 {
		panic("Expected size 4!")
	}
	var payload int32
	buf := bytes.NewReader(b)
	err := binary.Read(buf, binary.LittleEndian, &payload)
	if err != nil {
		// TODO: make safe
		panic(err)
	}
	return int(payload) // easier to work with ints
}

func readData(b []byte, wfmt WaveFmt) WaveData {
	wd := WaveData{}

	start := 36 + wfmt.ExtraParamSize
	subchunk2ID := b[start : start+4]
	wd.Subchunk2ID = subchunk2ID

	subsize := bits32ToInt(b[start+4 : start+8])
	wd.Subchunk2Size = subsize

	wd.RawData = b[start+8:]

	return wd
}

// Should we do n-channel separation at this point?
func parseRawData(wfmt WaveFmt, rawdata []byte) []Frame {
	bytesSampleSize := wfmt.BitsPerSample / 8
	// TODO: sanity-check that this is a power of 2? I think only those sample sizes are
	// possible

	frames := []Frame{}
	// read the chunks
	for i := 0; i < len(rawdata); i += bytesSampleSize {
		rawFrame := rawdata[i : i+bytesSampleSize]
		unscaledFrame := byteSizeToIntFunc[wfmt.BitsPerSample](rawFrame)
		scaled := scaleFrame(unscaledFrame, wfmt.BitsPerSample)
		frames = append(frames, scaled)
	}
	return frames
}

func scaleFrame(unscaled, bits int) Frame {
	maxV := maxValues[bits]
	return Frame(float64(unscaled) / float64(maxV))

}

// deleteJunk will remove the JUNK chunks if they are present
func deleteJunk(b []byte) []byte {
	var junkStart, junkEnd int

	for i := 0; i < len(b)-4; i++ {
		if strings.ToLower(string(b[i:i+4])) == "junk" {
			junkStart = i
		}

		if strings.ToLower(string(b[i:i+3])) == "fmt" {
			junkEnd = i
		}
	}

	if junkStart != 0 {
		cpy := make([]byte, len(b[0:junkStart]))
		copy(cpy, b[0:junkStart])
		cpy = append(cpy, b[junkEnd:]...)
		return cpy
	}

	return b
}

// readFmt parses the FMT portion of the WAVE file
// assumes the entire binary representation is passed!
func readFmt(b []byte) WaveFmt {
	wfmt := WaveFmt{}
	subchunk1ID := b[12:16]
	wfmt.Subchunk1ID = subchunk1ID

	subchunksize := bits32ToInt(b[16:20])
	wfmt.Subchunk1Size = subchunksize

	format := bits16ToInt(b[20:22])
	wfmt.AudioFormat = format

	numChannels := bits16ToInt(b[22:24])
	wfmt.NumChannels = numChannels

	sr := bits32ToInt(b[24:28])
	wfmt.SampleRate = sr

	br := bits32ToInt(b[28:32])
	wfmt.ByteRate = br

	ba := bits16ToInt(b[32:34])
	wfmt.BlockAlign = ba

	bps := bits16ToInt(b[34:36])
	wfmt.BitsPerSample = bps

	// parse extra (optional) elements..

	if subchunksize != 16 {
		// only for compressed files (non-PCM)
		extraSize := bits16ToInt(b[36:38])
		wfmt.ExtraParamSize = extraSize
		wfmt.ExtraParams = b[38 : 38+extraSize]
	}

	return wfmt
}

// TODO: make safe.
func readHeader(b []byte) WaveHeader {
	// the start of the bte slice..
	hdr := WaveHeader{}
	hdr.ChunkID = b[0:4]
	if string(hdr.ChunkID) != "RIFF" {
		panic("Invalid file")
	}

	chunkSize := b[4:8]
	var size uint32
	buf := bytes.NewReader(chunkSize)
	err := binary.Read(buf, binary.LittleEndian, &size)
	if err != nil {
		panic(err)
	}
	hdr.ChunkSize = int(size) // easier to work with ints

	format := b[8:12]
	if string(format) != "WAVE" {
		panic("Format should be WAVE")
	}
	hdr.Format = string(format)
	return hdr
}

var (
	// noteIndex for use in calculations where a user passes a note
	noteIndex = map[string]int{
		"a":  0,
		"a#": 1,
		"bb": 1,
		"b":  2,
		"c":  3,
		"c#": 4,
		"db": 4,
		"d":  5,
		"d#": 6,
		"eb": 6,
		"e":  7,
		"f":  8,
		"f#": 9,
		"gb": 9,
		"g":  10,
		"g#": 11,
		"ab": 11,
	}
)

var (
	s      = struct{}{}
	valid  = map[string]interface{}{"a": s, "b": s, "c": s, "d": s, "e": s, "f": s, "g": s, "#": s}
	digits = map[string]interface{}{"0": s, "1": s, "2": s, "3": s, "4": s, "5": s, "6": s, "7": s, "8": s, "9": s}
)

// ADSR creates an attack -> decay -> sustain -> release envelope
// time durations are passes as seconds.
// returns the value + the current time
func ADSR(maxamp, duration, attacktime, decaytime, sus, releasetime, controlrate float64, currentframe int) float64 {
	dur := duration * controlrate
	at := attacktime * controlrate
	dt := decaytime * controlrate
	rt := releasetime * controlrate
	cnt := float64(currentframe)

	amp := 0.0
	if cnt < dur {
		if cnt <= at {
			// attack
			amp = cnt * (maxamp / at)
		} else if cnt <= (at + dt) {
			// decay
			amp = ((sus-maxamp)/dt)*(cnt-at) + maxamp
		} else if cnt <= dur-rt {
			// sustain
			amp = sus
		} else if cnt > (dur - rt) {
			// release
			amp = -(sus/rt)*(cnt-(dur-rt)) + sus
		}
	}

	return amp
}

// NoteToFrequency turns a given note & octave into a frequency
// using Equal-Tempered tuning with reference pitch = A440
func NoteToFrequency(note string, octave int) float64 {
	// TODO: Allow for tuning systems other than Equal-Tempered A440?
	// clean the input
	note = strings.ToLower(strings.TrimSpace(note))
	ni := noteIndex[note]
	if ni >= 3 {
		// correct for octaves starting at C, not A.
		octave--
	}
	FR := 440.
	// we adjust the octave (-4) as the reference frequency is in the fourth octave
	// this effectively allows us to generate any octave above or below the reference octave
	return FR * math.Pow(2, float64(octave-4)+(float64(ni)/12.))
}

// parseNoteOctave returns the note + octave value
func parseNoteOctave(note string) (string, int, error) {
	note = strings.ToLower(note)
	notePart := strings.Map(func(r rune) rune {
		if _, ok := valid[string(r)]; !ok {
			return rune(-1)
		}
		return r
	}, note)

	digitPart := strings.Map(func(r rune) rune {
		if _, ok := digits[string(r)]; !ok {
			return rune(-1)
		}
		return r
	}, note[len(notePart):])

	octave, err := strconv.Atoi(digitPart)
	if err != nil {
		return "", 0, err
	}

	return notePart, octave, nil
}

// ParseNoteToFrequency tries to parse a string representation of a note+octave (e.g C#4)
// and will return a float64 frequency value using 'NoteToFrequency'
func ParseNoteToFrequency(note string) (float64, error) {
	nt, oct, err := parseNoteOctave(note)
	if err != nil {
		return -1, err
	}
	return NoteToFrequency(nt, oct), nil
}

// representation of the wave file, used by reader.go and writer.go

// Frame is a single float64 value of raw audio data
type Frame float64

/*

╔════════╤════════════════╤══════╤═══════════════════════════════════════════════════╗
║ Offset │ Field          │ Size │ -- start of header                                ║
╠════════╪════════════════╪══════╪═══════════════════════════════════════════════════╣
║ 0      │ ChunkID        │ 4    │                                                   ║
╟────────┼────────────────┼──────┼───────────────────────────────────────────────────╢
║ 4      │ ChunkSize      │ 4    │                                                   ║
╟────────┼────────────────┼──────┼───────────────────────────────────────────────────╢
║ 8      │ Format         │ 8    │                                                   ║
╟────────┼────────────────┼──────┼───────────────────────────────────────────────────╢
║ --     │ --             │ --   │ -- start of fmt                                   ║
╟────────┼────────────────┼──────┼───────────────────────────────────────────────────╢
║ 12     │ SubchunkID     │ 4    │                                                   ║
╟────────┼────────────────┼──────┼───────────────────────────────────────────────────╢
║ 16     │ SubchunkSize   │ 4    │                                                   ║
╟────────┼────────────────┼──────┼───────────────────────────────────────────────────╢
║ 20     │ AudioFormat    │ 2    │                                                   ║
╟────────┼────────────────┼──────┼───────────────────────────────────────────────────╢
║ 22     │ NumChannels    │ 2    │                                                   ║
╟────────┼────────────────┼──────┼───────────────────────────────────────────────────╢
║ 24     │ SampleRate     │ 4    │                                                   ║
╟────────┼────────────────┼──────┼───────────────────────────────────────────────────╢
║ 28     │ ByteRate       │ 4    │                                                   ║
╟────────┼────────────────┼──────┼───────────────────────────────────────────────────╢
║ 32     │ BlockAlign     │ 2    │                                                   ║
╟────────┼────────────────┼──────┼───────────────────────────────────────────────────╢
║ 34     │ BitsPerSample  │ 2    │                                                   ║
╟────────┼────────────────┼──────┼───────────────────────────────────────────────────╢
║ * 36   │ ExtraParamSize │ 2    │ Optional! Only when not PCM                       ║
╟────────┼────────────────┼──────┼───────────────────────────────────────────────────╢
║ * 38   │ ExtraParams    │ *    │ Optional! Only when not PCM                       ║
╟────────┼────────────────┼──────┼───────────────────────────────────────────────────╢
║ --     │ --             │ --   │ -- start of data, assuming PCM                    ║
╟────────┼────────────────┼──────┼───────────────────────────────────────────────────╢
║ 36     │ Subchunk2ID    │ 4    │ (offset by extra params of subchunk 1 if not PCM) ║
╟────────┼────────────────┼──────┼───────────────────────────────────────────────────╢
║ 40     │ SubchunkSize   │ 4    │ (offset by extra params of subchunk 1 if not PCM) ║
╟────────┼────────────────┼──────┼───────────────────────────────────────────────────╢
║ 44     │ Data           │ *    │ (offset by extra params of subchunk 1 if not PCM) ║
╚════════╧════════════════╧══════╧═══════════════════════════════════════════════════╝


*/

// Wave represents an entire .wav audio file
type Wave struct {
	WaveHeader
	WaveFmt
	WaveData
}

// WaveHeader describes the header each WAVE file should start with
type WaveHeader struct {
	ChunkID   []byte // should be RIFF on little-endian or RIFX on big-endian systems..
	ChunkSize int
	Format    string // sanity-check, should be WAVE (//TODO: keep as []byte?)
}

// WaveFmt describes the format of the sound-information in the data subchunks
type WaveFmt struct {
	Subchunk1ID    []byte // should contain "fmt"
	Subchunk1Size  int    // 16 for PCM
	AudioFormat    int    // PCM = 1 (Linear Quantization), if not 1, compression was used.
	NumChannels    int    // Mono 1, Stereo = 2, ..
	SampleRate     int    // 44100 for CD-Quality, etc..
	ByteRate       int    // SampleRate * NumChannels * BitsPerSample / 8
	BlockAlign     int    // NumChannels * BitsPerSample / 8 (number of bytes per sample)
	BitsPerSample  int    // 8 bits = 8, 16 bits = 16, .. :-)
	ExtraParamSize int    // if not PCM, can contain extra params
	ExtraParams    []byte // the actual extra params.
}

// WaveData contains the raw sound data
type WaveData struct {
	Subchunk2ID   []byte // Identifier of subchunk
	Subchunk2Size int    // size of raw sound data
	RawData       []byte // raw sound data itself
	Frames        []Frame
}

// NewWaveFmt can be used to generate a complete WaveFmt by calculating the remaining props
func NewWaveFmt(format, channels, samplerate, bitspersample int, extraparams []byte) WaveFmt {
	return WaveFmt{
		Subchunk1ID:    Format,
		Subchunk1Size:  16, // assume PCM for now //16
		AudioFormat:    format,
		NumChannels:    channels,
		SampleRate:     samplerate,
		ByteRate:       samplerate * channels * (bitspersample / 8.0),
		BlockAlign:     channels * (bitspersample / 8),
		BitsPerSample:  bitspersample,
		ExtraParamSize: len(extraparams),
		ExtraParams:    extraparams,
	}
}

// SetChannels changes the FMT to adapt to a new amount of channels
func (wfmt *WaveFmt) SetChannels(n uint) {
	wfmt.NumChannels = int(n)
	wfmt.ByteRate = (wfmt.SampleRate * wfmt.NumChannels * wfmt.BitsPerSample) / 8
	wfmt.BlockAlign = (wfmt.NumChannels * wfmt.BitsPerSample) / 8
}

// wavetable implementation

// FourierTable constructs a lookup table based on fourier addition with 'nharmns' harmonics
// If amps is provided, scales the harmonics by the provided amp
func FourierTable(nharms int, amps []float64, length int, phase float64) []float64 {
	table := make([]float64, length+2)
	phase *= tau

	for i := 0; i < nharms; i++ {
		for n := 0; n < len(table); n++ {
			amp := 1.0
			if i < len(amps) {
				amp = amps[i]
			}
			angle := float64(i+1) * (float64(n) * tau / float64(length))
			table[n] += (amp * math.Cos(angle+phase))
		}
	}
	return normalize(table)
}

// SawTable creates a sawtooth wavetable using Fourier addition
func SawTable(nharms, length int) []float64 {
	amps := make([]float64, nharms)
	for i := 0; i < len(amps); i++ {
		amps[i] = 1.0 / float64(i+1)
	}
	return FourierTable(nharms, amps, length, -0.25)
}

// SquareTable uses fourier addition to create a square waveform
func SquareTable(nharms, length int) []float64 {
	amps := make([]float64, nharms)
	for i := 0; i < len(amps); i += 2 {
		amps[i] = 1.0 / float64(i+1)
	}
	return FourierTable(nharms, amps, length, -0.25)
}

// TriangleTable uses fourier addition to create a triangle waveform
func TriangleTable(nharms, length int) []float64 {
	amps := make([]float64, nharms)
	for i := 0; i < nharms; i += 2 {
		amps[i] = 1.0 / (float64(i+1) * float64(i+1))
	}
	return FourierTable(nharms, amps, length, 0)
}

// Consts that appear in the .WAVE file format
var (
	ChunkID          = []byte{0x52, 0x49, 0x46, 0x46} // RIFF
	BigEndianChunkID = []byte{0x52, 0x49, 0x46, 0x58} // RIFX
	WaveID           = []byte{0x57, 0x41, 0x56, 0x45} // WAVE
	Format           = []byte{0x66, 0x6d, 0x74, 0x20} // FMT
	Subchunk2ID      = []byte{0x64, 0x61, 0x74, 0x61} // DATA
)

type intsToBytesFunc func(i int) []byte

var (
	// intsToBytesFm to map X-bit int to byte functions
	intsToBytesFm = map[int]intsToBytesFunc{
		16: int16ToBytes,
		32: int32ToBytes,
	}
)

// WriteFrames writes the slice to disk as a .wav file
// the WaveFmt metadata needs to be correct
// WaveData and WaveHeader are inferred from the samples however..
func WriteFrames(samples []Frame, wfmt WaveFmt, file string) error {
	return WriteWaveFile(samples, wfmt, file)
}

func WriteWaveFile(samples []Frame, wfmt WaveFmt, file string) error {
	f, err := os.Create(file)
	if err != nil {
		return err
	}
	defer f.Close()

	return WriteWaveToWriter(samples, wfmt, f)
}

func WriteWaveToWriter(samples []Frame, wfmt WaveFmt, writer io.Writer) error {
	wfb := fmtToBytes(wfmt)
	data, databits := framesToData(samples, wfmt)
	hdr := createHeader(data)

	_, err := writer.Write(hdr)
	if err != nil {
		return err
	}
	_, err = writer.Write(wfb)
	if err != nil {
		return err
	}
	_, err = writer.Write(databits)
	if err != nil {
		return err
	}

	return nil
}

func int16ToBytes(i int) []byte {
	b := make([]byte, 2)
	in := uint16(i)
	binary.LittleEndian.PutUint16(b, in)
	return b
}

func int32ToBytes(i int) []byte {
	b := make([]byte, 4)
	in := uint32(i)
	binary.LittleEndian.PutUint32(b, in)
	return b
}

func framesToData(frames []Frame, wfmt WaveFmt) (WaveData, []byte) {
	b := []byte{}
	raw := samplesToRawData(frames, wfmt)

	// We receive frames but have to store the size of the samples
	// The size of the samples is frames / channels..
	subchunksize := (len(frames) * wfmt.NumChannels * wfmt.BitsPerSample) / 8
	subBytes := int32ToBytes(subchunksize)

	// construct the data part..
	b = append(b, Subchunk2ID...)
	b = append(b, subBytes...)
	b = append(b, raw...)

	wd := WaveData{
		Subchunk2ID:   Subchunk2ID,
		Subchunk2Size: subchunksize,
		RawData:       raw,
		Frames:        frames,
	}
	return wd, b
}

func floatToBytes(f float64, nBytes int) []byte {
	bits := math.Float64bits(f * math.Pow10(-307) * math.Pow10(-1))
	bs := make([]byte, 8)
	binary.LittleEndian.PutUint64(bs, bits)
	// trim padding
	switch nBytes {
	case 2:
		return bs[:2]
	case 4:
		return bs[:4]
	}
	return bs
}

// Turn the samples into raw data...
func samplesToRawData(samples []Frame, props WaveFmt) []byte {
	raw := []byte{}
	for _, s := range samples {
		// the samples are scaled - rescale them?
		rescaled := rescaleFrame(s, props.BitsPerSample)
		bits := intsToBytesFm[props.BitsPerSample](rescaled)
		raw = append(raw, bits...)
	}
	return raw
}

// rescale frames back to the original values..
func rescaleFrame(s Frame, bits int) int {
	rescaled := float64(s) * float64(maxValues[bits])
	return int(rescaled)
}

func fmtToBytes(wfmt WaveFmt) []byte {
	b := []byte{}

	subchunksize := int32ToBytes(wfmt.Subchunk1Size)
	audioformat := int16ToBytes(wfmt.AudioFormat)
	numchans := int16ToBytes(wfmt.NumChannels)
	sr := int32ToBytes(wfmt.SampleRate)
	br := int32ToBytes(wfmt.ByteRate)
	blockalign := int16ToBytes(wfmt.BlockAlign)
	bitsPerSample := int16ToBytes(wfmt.BitsPerSample)

	b = append(b, wfmt.Subchunk1ID...)
	b = append(b, subchunksize...)
	b = append(b, audioformat...)
	b = append(b, numchans...)
	b = append(b, sr...)
	b = append(b, br...)
	b = append(b, blockalign...)
	b = append(b, bitsPerSample...)

	return b
}

// turn the sample to a valid header
func createHeader(wd WaveData) []byte {
	// write chunkID
	bits := []byte{}

	chunksize := 36 + wd.Subchunk2Size
	cb := int32ToBytes(chunksize)

	bits = append(bits, ChunkID...) // in theory switch on endianness..
	bits = append(bits, cb...)
	bits = append(bits, WaveID...)

	return bits
}

//////END CREDITS ----https://github.com/DylanMeeus/GoAudio/

func Float642Frame(floats []float64) []Frame {
	Frames := []Frame{}
	for i := 0; i < len(floats); i++ {
		Frames = append(Frames, Frame(floats[i]))
	}
	return Frames
}

func Frame2Float64(Frames []Frame) []float64 {
	Floats := []float64{}
	for i := 0; i < len(Frames); i++ {
		Floats = append(Floats, float64(Frames[i]))
	}
	return Floats

}

func StripPadding(data []byte, size int) []byte {
	var nopadding []byte
	var j int
	switch size {
	case 2:
		nopadding = data[:len(data)-2]
	case 4:
		nopadding = data[:len(data)-4]
	case 8:
		nopadding = data[:len(data)-8]
	}
	j = len(nopadding)
	for i := len(nopadding); i <= len(nopadding); i = i - size {
		if !bytes.Equal(nopadding[i-size*2:i-size], nopadding[i-size:i]) {
			//Trailing NOOP's patch
			j = i
			break
			//nopadding = append(nopadding, bytes[i])
		}
	}
	if nopadding[j] == 0 {
		nopadding = nopadding[:j-1] //use pipe if there are more.
	} else {
		nopadding = nopadding[:j]
	}

	return nopadding
}

func WavToMp3(wavFileName, mp3FileName string, wfmt WaveFmt) {

	err := ffmpeg.Input(wavFileName).
		Output(mp3FileName, ffmpeg.KwArgs{"ab": "320k", "ar": wfmt.SampleRate, "ac": wfmt.NumChannels}).
		OverWriteOutput().ErrorToStdOut().Run()
	if err != nil {
		panic("ffmepg - MP3 conversion error")
	}
}

func Mp3toWav(mp3Filename string, WavFilename string) { //, SampleRate int, NbChannels int) {
	err := ffmpeg.Input(mp3Filename).
		Output(WavFilename, ffmpeg.KwArgs{"ab": "320k", "c:a": "pcm_s16le"}). //"ar": SampleRate, "ac": NbChannels, "c:a": "pcm_s16le"}).
		OverWriteOutput().ErrorToStdOut().Run()
	if err != nil {
		panic("ffmepg - wav decompression error")
	}
}

func InitializeWav(Original string, Initialized string, SampleRate int, NbChannels int) {
	err := ffmpeg.Input(Original).
		Output(Initialized, ffmpeg.KwArgs{"ab": "320k", "ar": SampleRate, "ac": NbChannels, "c:a": "pcm_s16le"}).
		OverWriteOutput().ErrorToStdOut().Run()
	if err != nil {
		panic("ffmepg - wav decompression error")
	}
}

func FileChecksum(file string) string {

	bytes, err := os.ReadFile(file)

	if err != nil {
		panic(err)
	}

	Checksum := md5.New()
	Checksum.Write(bytes)

	return hex.EncodeToString(Checksum.Sum(nil))
}

func ReadDiffFile(MP3DiffFileName string) []float64 {
	NbEntriesDiffFile, err := strconv.Atoi(strings.Split(MP3DiffFileName, "||")[2])
	if err != nil {
		panic(err)
	}
	DiffFile := make([]float64, NbEntriesDiffFile)
	file, err := os.Open("DATABASE/" + MP3DiffFileName)
	if err != nil {
		panic(err)
	}
	reader := io.Reader(file)
	error := binary.Read(reader, binary.LittleEndian, DiffFile)
	//ERROR...EMPTY.! TODO!
	if error != nil {
		panic(error)
	}
	file.Close()
	return DiffFile
}

func ReadDB(md5Sum string) (Database, string) {
	var Entry Database
	var filename string
	var CompleteFilename string
	var MP3DiffFileName string
	separator := make([]byte, 64)

	files := HuntDBDir()
	for _, name := range files { //TODO:Think about it more (files) and break.
		filename = name[:32]
		if filename == md5Sum[:32] {
			MP3DiffFileName = name
		}
		filename = name[:20]
		if filename == md5Sum[:20] && CompleteFilename == "" {
			CompleteFilename = name
		}

	}
	if MP3DiffFileName != "" || CompleteFilename != "" {

		if _, err := os.Stat(MP3DiffFileName); err == nil { //we just need one of the two.
			return Entry, MP3DiffFileName
		}

		file, err := os.Open("DATABASE/" + CompleteFilename)
		if err != nil {
			panic(err)
		}
		Entry.md5Sum = md5Sum
		reader := io.Reader(file)
		NbEntriesBandPassFilter, err := strconv.Atoi(strings.Split(CompleteFilename, "||")[1])
		if err != nil {
			panic(err)
		}
		NbEntriesMissingBits, err := strconv.Atoi(strings.Split(CompleteFilename, "||")[2])
		if err != nil {
			panic(err)
		}
		BandPassEntries := make([]float64, NbEntriesBandPassFilter)
		error := binary.Read(reader, binary.LittleEndian, BandPassEntries)
		if error != nil {
			panic(err)
		}
		Entry.BandpassFilter = BandPassEntries
		error = binary.Read(reader, binary.LittleEndian, separator)
		if error != nil {
			panic(error)
		}
		MissingBitsEntries := make([]float64, NbEntriesMissingBits)
		error = binary.Read(reader, binary.LittleEndian, MissingBitsEntries)
		if error != nil {
			panic(err)
		}
		Entry.MissingBits = MissingBitsEntries

		file.Close()
	}
	return Entry, MP3DiffFileName
}

func HuntDBDir() []string {
	file, err := os.Open("DATABASE/.")
	if err != nil {
		log.Fatalf("failed opening directory: %s", err)
	}
	defer file.Close()

	list, _ := file.Readdirnames(0) // 0 to read all files and folders

	return list
}

func WriteEntryDB(Entry Database, RebuildEntryMP3 []float64) {
	separator := make([]byte, 64)
	f, err := os.Create("DATABASE/" + Entry.md5Sum[:20] + "||" + strconv.Itoa(len(Entry.BandpassFilter)) + "||" + strconv.Itoa(len(Entry.MissingBits)))
	if err != nil {
		panic(err)
	}
	g, err := os.Create("DATABASE/" + Entry.md5Sum + "||DIFF||" + strconv.Itoa(len(RebuildEntryMP3)))
	if err != nil {
		panic(err)
	}

	err = binary.Write(f, binary.LittleEndian, Entry.BandpassFilter)
	if err != nil {
		panic(err)
	}

	//adding the separator
	err = binary.Write(f, binary.LittleEndian, separator)
	if err != nil {
		panic(err)
	}

	err = binary.Write(f, binary.LittleEndian, Entry.MissingBits)
	if err != nil {
		panic(err)
	}

	f.Close()

	err = binary.Write(g, binary.LittleEndian, RebuildEntryMP3) ///
	if err != nil {
		panic(err)
	}

	g.Close()
}

func ReadWriteModded(OriginalWav string, OriginalData string, Modded string, Modded_MP3 string) ([]float64, []float64, []float64, Wave, string) {
	//var recovered_modded [][]byte
	fmt.Println("Reading...", OriginalWav)
	WavStruct, err := ReadWaveFile(OriginalWav)
	if err == nil {
		Generated, OutOfBoundsFrames := generate(OriginalData, int64(len(WavStruct.Frames)), WavStruct.WaveFmt)
		fmt.Println("Writing...", Modded)

		BandpassFilter := Lowpass(Highpass(Frame2Float64(WavStruct.Frames), 10000, 0, float64(WavStruct.SampleRate)), 6000, 0, float64(WavStruct.SampleRate)) //1000Hz to 15KHz

		MergedFrames := []float64{}
		for i := 0; i < len(BandpassFilter); i++ {
			MergedFrames = append(MergedFrames, (BandpassFilter[i] + Generated[i]))
		}

		WriteWaveFile(Float642Frame(MergedFrames), WavStruct.WaveFmt, Modded) //THIS@

		WavToMp3(Modded, Modded_MP3, WavStruct.WaveFmt)

		Checksum := FileChecksum(Modded_MP3)

		return BandpassFilter, OutOfBoundsFrames, MergedFrames, WavStruct, Checksum
	} else {
		panic(err)
	}
}

/*func RebuildFromDiff(Wav) {
	var RebuildMP3Diff []float64
	//TODO: DO!
	//InitializeWav(Wav_OutFile, MP3DiffFileName, WaveStruct.SampleRate, WaveStruct.NumChannels) //CHECK THIS>!
	DiffWaveStruct, err := ReadWaveFile(Wav_OutFile)
	if err != nil {
		panic(err)
	}
	MP3Frames := Frame2Float64(parseRawData(DiffWaveStruct.WaveFmt, DiffWaveStruct.RawData))
	MaxIndexTemp := len(MP3Frames)

	_, DiffFilename := ReadDB(FileChecksum(Modded_MP3))

	RebuiltMP3Diff := ReadDiffFile(DiffFilename)
	i := 0
	for _, DiffFrame := range RebuiltMP3Diff {
		//READ AND CORRECT MP3 FRAMES
		if i < MaxIndexTemp {
			RebuildMP3Diff = append(RebuildMP3Diff, (DiffFrame + MP3Frames[i]))
		} else {
			RebuildMP3Diff = append(RebuildMP3Diff, DiffFrame)
		}
		i++
	}
	//WriteWaveFile(Float642Frame(RebuiltMP3Diff), DiffWaveStruct.WaveFmt, MP3DiffFileName)
	os.Remove(Wav_OutFile)
	WriteWaveFile(Float642Frame(RebuildMP3Diff), DiffWaveStruct.WaveFmt, Wav_OutFile)

}*/

func BuildWave(Modded_MP3 string, Modded string, MergedFrames []float64, WaveStruct Wave, Wav_OutFile string) []float64 {
	var RebuiltMP3Diff []float64
	Mp3toWav(Modded_MP3, Wav_OutFile) //, WaveStruct.SampleRate, WaveStruct.NumChannels) // save
	DiffWaveStruct, err := ReadWaveFile(Wav_OutFile)
	if err != nil {
		panic(err)
	}
	MP3Frames := Frame2Float64(parseRawData(DiffWaveStruct.WaveFmt, DiffWaveStruct.RawData))
	MaxIndexTemp := len(MP3Frames)
	i := 0
	for _, MergedFrame := range MergedFrames {
		if i < MaxIndexTemp {
			RebuiltMP3Diff = append(RebuiltMP3Diff, (MergedFrame - MP3Frames[i]))
		} else {
			RebuiltMP3Diff = append(RebuiltMP3Diff, MergedFrame)
		}
		i++
	}
	WriteWaveFile(Float642Frame(RebuiltMP3Diff), DiffWaveStruct.WaveFmt, "DIFF-RECOVERED.wav")
	return RebuiltMP3Diff
}

func RebuildWaveFromMP3(Modded_MP3 string, Modded string, MP3DiffFileName string, Wav_OutFile string) ([]float64, Wave) {
	var RebuildMP3Diff []float64
	var DiffWaveStruct Wave

	if _, err := os.Stat(MP3DiffFileName); os.IsNotExist(err) {
		Mp3toWav(Modded_MP3, Wav_OutFile)
		DiffWaveStruct, err := ReadWaveFile(Wav_OutFile)
		if err != nil {
			panic(err)
		}
		MP3Frames := Frame2Float64(parseRawData(DiffWaveStruct.WaveFmt, DiffWaveStruct.RawData))
		MaxIndexTemp := len(MP3Frames)

		_, MP3DiffFileName := ReadDB(FileChecksum(Modded_MP3))

		RebuiltMP3Diff := ReadDiffFile(MP3DiffFileName)

		i := 0
		for _, DiffFrame := range RebuiltMP3Diff {
			//READ AND CORRECT MP3 FRAMES
			if i < MaxIndexTemp {
				RebuildMP3Diff = append(RebuildMP3Diff, (DiffFrame + MP3Frames[i]))
			} else {
				RebuildMP3Diff = append(RebuildMP3Diff, DiffFrame)
			}
			i++
		}
		/*
			i := 0
			for _, MergedFrame := range MergedFrames {
				if i < MaxIndexTemp {
					RebuiltMP3Diff = append(RebuiltMP3Diff, (MergedFrame - MP3Frames[i]))
				} else {
					RebuiltMP3Diff = append(RebuiltMP3Diff, MergedFrame)
				}
				i++
			}*/
		WriteWaveFile(Float642Frame(RebuildMP3Diff), DiffWaveStruct.WaveFmt, "DIFF-RECOVERED.wav")
		WriteWaveFile(Float642Frame(RebuildMP3Diff), DiffWaveStruct.WaveFmt, Wav_OutFile)
		//os.Remove("TEMP.wav")
	} else {
		//InitializeWav(Wav_OutFile, MP3DiffFileName, WaveStruct.SampleRate, WaveStruct.NumChannels) //CHECK THIS>!
		DiffWaveStruct, err := ReadWaveFile(Wav_OutFile)
		if err != nil {
			panic(err)
		}
		MP3Frames := Frame2Float64(parseRawData(DiffWaveStruct.WaveFmt, DiffWaveStruct.RawData))
		MaxIndexTemp := len(MP3Frames)

		_, DiffFilename := ReadDB(FileChecksum(Modded_MP3))

		RebuiltMP3Diff := ReadDiffFile(DiffFilename)
		i := 0
		for _, DiffFrame := range RebuiltMP3Diff {
			//READ AND CORRECT MP3 FRAMES
			if i < MaxIndexTemp {
				RebuildMP3Diff = append(RebuildMP3Diff, (DiffFrame + MP3Frames[i]))
			} else {
				RebuildMP3Diff = append(RebuildMP3Diff, DiffFrame)
			}
			i++
		}
		//WriteWaveFile(Float642Frame(RebuiltMP3Diff), DiffWaveStruct.WaveFmt, MP3DiffFileName)
		os.Remove(Wav_OutFile)
		WriteWaveFile(Float642Frame(RebuildMP3Diff), DiffWaveStruct.WaveFmt, Wav_OutFile)
	}
	return RebuildMP3Diff, DiffWaveStruct
}

func WriteDB(Entries []Database, BandpassFilter []float64, OutOfBoundsFrames []float64, WavStruct Wave, RebuildEntryMP3 []float64, Checksum string, Save bool) ([]Database, []string) {
	var Entry Database
	RAM_Needed := (len(BandpassFilter) + len(OutOfBoundsFrames)) * 16 //float64 64 bits in bytes * 2 assignments
	runtime.GC()                                                      //Garbage Collector
	var m runtime.MemStats
	runtime.ReadMemStats(&m) //Trip to comments to test disk readDB
	//EntriesBandPassFilter := make(map[string][]float64)
	//EntriesOutOfBoundsFrames := make(map[string][]float64)

	Entry = Database{
		Checksum,
		BandpassFilter,
		OutOfBoundsFrames,
	}

	KeysEntries := []string{}

	if (m.Sys - m.Alloc) > uint64(RAM_Needed) { //There is enough RAM to assign it to RAM.
		Entries = append(Entries, Entry)
		KeysEntries = append(KeysEntries, Checksum)
	} else {
		Entries = nil
		KeysEntries = nil
		runtime.GC()
	}
	if Save {
		WriteEntryDB(Entry, RebuildEntryMP3) //Always write to file
	}

	return Entries, KeysEntries
}

func SwitchRamOrFile(CheckSum string, Entries []Database, KeysEntries []string) ([]float64, []float64) {
	// //from RAM or fallback on fileDB
	var BandpassFilter []float64
	var OutOfBoundsFrames []float64
	Found := false
	if Entries != nil {
		i := 0
		for _, KeyChecksum := range KeysEntries {
			if CheckSum == KeyChecksum {
				Found = true
				break
			}
			i++
		}

		if Found { //grab it from the RAM
			Entry := Entries[i]
			BandpassFilter = Entry.BandpassFilter
			OutOfBoundsFrames = Entry.MissingBits
		} else { //from disk then
			Entry, MP3DiffFileName := ReadDB(CheckSum)
			if MP3DiffFileName != "" { //Prefer rebuilding the MP3
				///)(*&^%$#@!HERE)
			} else {
				BandpassFilter = Entry.BandpassFilter
				OutOfBoundsFrames = Entry.MissingBits
			}
		}
	}
	return BandpassFilter, OutOfBoundsFrames
}

func Hunt(Modded string, Modded_MP3 string, Wav_OutFile string, WavStruct Wave, BandPassFilter []float64, OutOfBoundsFrames []float64, MergedFrames []float64) [][]byte {
	var recovered_modded [][]byte
	//Mp3toWav(Modded_MP3, Wav_OutFile, WavStruct.SampleRate, WavStruct.NumChannels) //HERE

	fmt.Println("Hunting...", Wav_OutFile)
	WavStructModded, err := ReadWaveFile(Wav_OutFile)
	size := WavStructModded.BitsPerSample / 8
	if err == nil {
		ModdedMergedFrames := Frame2Float64(parseRawData(WavStructModded.WaveFmt, WavStructModded.RawData))
		if len(ModdedMergedFrames) == len(BandPassFilter) {
			j := 0
			for i := 0; i < len(BandPassFilter); i++ {
				if MergedFrames[i]-BandPassFilter[i] != 0 {
					recovered_modded = append(recovered_modded, floatToBytes(MergedFrames[i]-BandPassFilter[i], size))
				} else {
					if j < len(OutOfBoundsFrames) { //Generated[i] == 0 {
						//recovered_modded = append(recovered_modded, floatToBytes(MergedFrames[i]-BandpassFilter[i], size))
						recovered_modded = append(recovered_modded, floatToBytes(OutOfBoundsFrames[j], size))
						j++
					}
				}
			}
		}
	}
	return recovered_modded
}

func GoHunting(OriginalWav string, OriginalData string, Modded string, Modded_MP3 string, Wav_OutFile string, Diff_Recovered string, Entries []Database) ([][]byte, []Database) {

	//BandPassFilter, OutOfBoundsFrames, MergedFrames, WaveStruct, CheckSum := ReadWriteModded(OriginalWav, OriginalData, Modded, Modded_MP3)
	RebuildEntryMP3, WaveStruct := RebuildWaveFromMP3(Modded_MP3, Modded, Diff_Recovered, Wav_OutFile)
	Entry, _ := ReadDB(FileChecksum(Modded_MP3))
	recovered_modded := Hunt(Modded, Modded_MP3, Wav_OutFile, WaveStruct, Entry.BandpassFilter, Entry.MissingBits, RebuildEntryMP3)
	return recovered_modded, Entries
}

func ReadWrite(OriginalWav string, OriginalData string, Modded string, Modded_MP3 string, Wav_OutFile string, Diff_Recovered string, Entries []Database) []Database {
	if _, err := os.Stat("DATABASE"); os.IsNotExist(err) {
		err := os.Mkdir("DATABASE", os.ModePerm)
		if err != nil {
			panic(err)
		}
	}

	BandPassFilter, OutOfBoundsFrames, MergedFrames, WaveStruct, CheckSum := ReadWriteModded(OriginalWav, OriginalData, Modded, Modded_MP3)
	RebuildEntryMP3 := BuildWave(Modded_MP3, Modded, MergedFrames, WaveStruct, Wav_OutFile)
	Entries, _ = WriteDB(Entries, BandPassFilter, OutOfBoundsFrames, WaveStruct, RebuildEntryMP3, CheckSum, true)

	return Entries
}

func GenerateFrequencyBreakpoints(frequency int) ([]Breakpoint, float64) {

	var Breakpoints []Breakpoint

	Hertz := 1 / float64(frequency)

	Breakpoints = append(Breakpoints, Breakpoint{0, 0.5})
	//Breakpoints = append(Breakpoints, Breakpoint{float64(Period), 0.5}) // corresponds to 0 on the sine wave
	Breakpoints = append(Breakpoints, Breakpoint{Hertz, 0.5})

	return Breakpoints, (1 / float64(frequency)) / 2 //Period

}

func GenerateAmplitudesBreakpoints(Period float64) []Breakpoint {
	var Breakpoints []Breakpoint

	Breakpoints = append(Breakpoints, Breakpoint{Period / 2, -1})
	Breakpoints = append(Breakpoints, Breakpoint{Period / 2 * Period, 1})

	return Breakpoints

}

func generate_wave(dur int, shape Shape, ampStream, freqStream *BreakpointStream, wfmt WaveFmt) []Frame {
	reqFrames := dur * wfmt.SampleRate
	frames := make([]Frame, reqFrames)
	osc, err := NewOscillator(wfmt.SampleRate, shape)
	if err != nil {
		panic(err)
	}

	for i := range frames {
		amp := ampStream.Tick()
		freq := freqStream.Tick()
		frames[i] = Frame(amp * osc.Tick(freq))
	}

	return frames
}

func generate_file(filename string, frequency, bits, duration int, shape Shape) WaveFmt {

	// Generate an oscillator of a given shape and duration
	// Modified by amplitude / frequency breakpoints

	wfmt := NewWaveFmt(1, 1, frequency, bits, nil) //stereo

	freqPoints, Period := GenerateFrequencyBreakpoints(wfmt.SampleRate)

	freqStream, err := NewBreakpointStream(freqPoints, wfmt.SampleRate)
	if err != nil {
		panic(err)
	}

	ampPoints := GenerateAmplitudesBreakpoints(Period)

	ampStream, err := NewBreakpointStream(ampPoints, wfmt.SampleRate)
	if err != nil {
		panic(err)
	}

	// create wave file sampled at 48Khz w/ 32-bit frames

	frames := generate_wave(duration, shape, ampStream, freqStream, wfmt)
	WriteFrames(frames, wfmt, filename)

	return wfmt
}

func Erase(filename string) {
	err := os.Remove(filename)
	if err != nil {
		panic(err) //Handle this better in the future.
	}
}

func Recover(Modded_MP3 string, recovered_modded [][]byte, WaveStruct Wave) {
	f, err := os.Create(strings.Split(Modded_MP3, ".")[0] + "-RECOVERED.data")
	if err != nil {
		panic(err)
	}

	writer := io.Writer(f)
	var data []byte

	for i := 0; i < len(recovered_modded); i++ {
		for j := 0; j < len(recovered_modded[i]); j++ {
			data = append(data, recovered_modded[i][j])
		}

	}
	writer.Write(StripPadding(data, WaveStruct.BitsPerSample/8))
	f.Close()
}

func GetFreePort(port string) (string, net.IP) {
	addr, _ := net.ResolveTCPAddr("tcp", "localhost:"+port)

	l, _ := net.ListenTCP("tcp", addr)
	defer l.Close()

	return strconv.Itoa(l.Addr().(*net.TCPAddr).Port), l.Addr().(*net.TCPAddr).IP
}

func FetchRootCA(Conn *net.TCPConn) []byte {

	bRootCa := make([]byte, 10485760) //10MB

	n, err := Conn.Read(bRootCa)
	if err != nil {
		panic(err)
	}

	return bRootCa[:n]

}

func PutRootCA(Conn *net.TCPConn, CaCertificate []byte) {

	_, err := Conn.Write(CaCertificate)
	if err != nil {
		panic(err)
	}
}

func GetlocalIP() net.IP {
	ifaces, _ := net.Interfaces()
	// handle err
	for _, i := range ifaces {
		addrs, _ := i.Addrs()
		// handle err
		for _, addr := range addrs {
			var ip net.IP
			switch v := addr.(type) {
			case *net.IPNet:
				ip = v.IP
			case *net.IPAddr:
				ip = v.IP
			}
			if ip.String() != "127.0.0.1" && ip.String() != "::1" {
				return ip
			}
		}
	}
	return nil
}

func StartSSLClient(Mp3_Modded string, ip string, port string, External_IP string) { //, CertFile string, KeyFile string) {
	//var SSL_packet []byte
	var Uploaded_File []byte
	var NbEntriesDiffFile string

	//fmt.Println("CLIENT_STARTED!")

	//CertFile = "Client/cert.pem"
	//KeyFile = "Client/private.key"
	//ForgeCertificate("Client") //for testing purposses
	lport, _ := GetFreePort("0")
	lport_int, _ := strconv.Atoi(lport)

	var laddr net.TCPAddr
	var raddr net.TCPAddr

	laddr.IP = GetlocalIP()
	laddr.Port = lport_int
	raddr.IP = net.ParseIP(ip)
	rport, _ := strconv.Atoi(port)
	raddr.Port = rport + 1 //oops....

	//laddr.Zone = ""

	TCP_Conn, err := net.DialTCP("tcp", &laddr, &raddr)
	if err != nil {
		panic(err)
	}

	Server_CA := FetchRootCA(TCP_Conn)

	f, err := os.Create("ServerCA.crt")
	if err != nil {
		panic(err)
	}
	f.Write(Server_CA)
	f.Close()

	IP := net.ParseIP(External_IP) //GetlocalIP() //todo...adjust to your reality!
	fmt.Println(IP.String())

	CaCertificate, CAPrivateKey, _ := ForgeCACertificate(IP.String(), true, false) //Self-Signed CA

	PutRootCA(TCP_Conn, CaCertificate)

	TCP_Conn.Close()

	time.Sleep(time.Millisecond * 1000) ///TODO...DROP this on the internet.

	Certificate, _, Private_Key_Pem_bytes := ForgeCertificate(IP.String(), false, true, CaCertificate, CAPrivateKey) //CA Signed Certificate

	x509Certificate, err := x509.ParseCertificate(Certificate)
	if err != nil {
		panic(err)
	}

	x509ServerCACertificate, err := x509.ParseCertificate(Server_CA)
	if err != nil {
		panic(err)
	}

	//x509CACertificate, err := x509.ParseCertificate(CaCertificate)
	//if err != nil {
	//	panic(err)
	//}

	//x509ClientCACertificate, err := x509.ParseCertificate(CaCertificate)
	//if err != nil {
	//	panic(err)
	//}
	//Client_CA, _ := os.ReadFile("/home/jordan/Desktop/Node1/RootCA/Node1_CA.crt") //and 1 more

	//Certificate, err := tls.LoadX509KeyPair(CertFile, KeyFile)
	//if err != nil {
	//	panic(err)
	//}
	//ParsedCertificate, err := x509.ParseCertificate(Certificate.Leaf.Raw)
	//if err != nil {
	//	panic(err)
	//}

	var Certificate_Pem pem.Block
	Certificate_Pem.Type = "CERTIFICATE"
	Certificate_Pem.Bytes = x509Certificate.Raw

	var Private_Key_Pem pem.Block
	Private_Key_Pem.Type = "PRIVATE KEY"
	Private_Key_Pem.Bytes = Private_Key_Pem_bytes

	roots := x509.NewCertPool()
	roots.AddCert(x509ServerCACertificate)
	//roots.AddCert(x509CACertificate)
	//roots.AddCert(x509Certificate)
	Configuration := tls.Config{}
	Configuration.RootCAs = roots
	//tls_Certificate, err := tls.X509KeyPair(pem.EncodeToMemory(&Certificate_Pem), pem.EncodeToMemory(&Private_Key_Pem))
	if err != nil {
		panic(err)
	}

	//tls_Certificate.PrivateKey = PrivateKey //HERE

	//Configuration.Certificates = append(Configuration.Certificates, tls_Certificate)

	//Configuration.InsecureSkipVerify = true
	Configuration.MinVersion = tls.VersionTLS12
	Configuration.MaxVersion = tls.VersionTLS13
	//Configuration.ClientAuth = tls.RequireAndVerifyClientCert
	//AllowedCiphers := []uint16{tls.TLS_CHACHA20_POLY1305_SHA256}
	//Configuration.CipherSuites = AllowedCiphers

	Configuration.ServerName = x509ServerCACertificate.Subject.CommonName
	//tls.Client()

	/*_ = &tls.Config{
		// Set InsecureSkipVerify to skip the default validation we are
		// replacing. This will not disable VerifyConnection.
		InsecureSkipVerify: true,
		VerifyConnection: func(cs tls.ConnectionState) error {
			opts := x509.VerifyOptions{
				DNSName:       cs.ServerName,
				Intermediates: x509.NewCertPool(),
			}
			for _, cert := range cs.PeerCertificates[1:] {
				opts.Intermediates.AddCert(cert)
			}
			_, err := cs.PeerCertificates[0].Verify(opts)
			return err
		},
	}*/

	host := ip
	net_Conn, err := net.Dial("tcp4", host+":"+port)
	if err != nil {
		panic("failed to connect: " + err.Error())
	}
	tls_Conn := tls.Client(net_Conn, &Configuration)

	err = tls_Conn.SetDeadline(time.Now().Add(time.Minute)) //1 minute and a half
	if err != nil {
		panic(err)
	}
	defer tls_Conn.Close()

	// ////////////////////////////////////TODO
	ConnectInfos := ip + ":" + port
	fmt.Println("Establishing a connection with ", ConnectInfos)

	MP3_Bytes, err := os.ReadFile(Mp3_Modded)
	if err != nil {
		panic(err)
	}
	fmt.Println("Sending...", Mp3_Modded)
	//time.Sleep(time.Millisecond * 200)
	/*err = tls_Conn.Handshake()
	if err != nil {
		panic(err)
	}
	for {
		if !tls_Conn.ConnectionState().HandshakeComplete {
			time.Sleep(time.Millisecond * 200)
		} else {
			break
		}
	}*/
	_, err = tls_Conn.Write(MP3_Bytes)
	if err != nil {
		panic(err)
	}
	fmt.Println("Receiving...")
	buffer := make([]byte, 1073741824) //1Gig
	_, err = tls_Conn.Read(buffer)
	//NbEntriesDiffFile = strings.Split(string(buffer2), "||DIFF||")[1]

	fmt.Println("Receving Database ...")

	if _, err := os.Stat("DATABASE"); os.IsNotExist(err) {
		err := os.Mkdir("DATABASE", os.ModePerm)
		if err != nil {
			panic(err)
		}
	}

	Downloaded := md5.New()
	Downloaded.Write(MP3_Bytes)

	fmt.Println("Writing DATABASE ...")

	f, err = os.Create(hex.EncodeToString(Downloaded.Sum(nil)) + "||DIFF||" + NbEntriesDiffFile) //for test purposes
	if err != nil {
		panic(err)
	}

	f.Write(Uploaded_File)

	f.Close()

}

func RandStringBytesMaskImprSrcSB(n int) string {
	const letterBytes = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
	const (
		letterIdxBits = 6                    // 6 bits to represent a letter index
		letterIdxMask = 1<<letterIdxBits - 1 // All 1-bits, as many as letterIdxBits
		letterIdxMax  = 63 / letterIdxBits   // # of letter indices fitting in 63 bits
	)

	var src = rand2.NewSource(time.Now().UnixNano())

	sb := strings.Builder{}
	sb.Grow(n)
	// A src.Int63() generates 63 random bits, enough for letterIdxMax characters!
	for i, cache, remain := n-1, src.Int63(), letterIdxMax; i >= 0; {
		if remain == 0 {
			cache, remain = src.Int63(), letterIdxMax
		}
		if idx := int(cache & letterIdxMask); idx < len(letterBytes) {
			sb.WriteByte(letterBytes[idx])
			i--
		}
		cache >>= letterIdxBits
		remain--
	}

	return sb.String()
}

func ForgeCertificate(IP string, ca bool, CASigned bool, CaCertificate []byte, CAPrivateKey *ecdsa.PrivateKey) ([]byte, *ecdsa.PrivateKey, []byte) {

	random := rand.Reader
	var Private_Key_Pem []byte
	var Certificate []byte
	var IPAddresses []net.IP
	var Organizations []string
	var DNSs []string
	var err error

	net_IP := net.ParseIP(IP)

	IPAddresses = append(IPAddresses, net_IP)
	HostName, _ := os.Hostname()

	Organization := string(RandStringBytesMaskImprSrcSB(rand2.Intn(32-8) + 8))
	Organizations = append(Organizations, Organization)
	Private_Key, _ := ecdsa.GenerateKey(elliptic.P521(), random)

	now := time.Now()
	now = now.Add(-1 * 60 * 60 * 24 * 1000 * 1000 * 1000)
	then := now.Add(60 * 60 * 24 * 365 * 1000 * 1000 * 1000)

	//fmt.Println(PublicKey.Equal(PrivateKey.Public()))

	DNSs = append(DNSs, "*."+HostName)
	DNSs = append(DNSs, HostName)

	rand2.Seed(time.Now().UTC().UnixNano())

	template := x509.Certificate{
		SerialNumber: big.NewInt(int64(rand2.Intn(math.MaxInt64))),
		Subject: pkix.Name{
			CommonName:   HostName,
			Organization: Organizations,
		},
		NotBefore: now,
		NotAfter:  then,
		//SubjectKeyId:          []byte{1, 2, 3, 4},
		KeyUsage:              x509.KeyUsageCertSign | x509.KeyUsageKeyEncipherment | x509.KeyUsageDigitalSignature,
		BasicConstraintsValid: true,
		IsCA:                  ca,
		DNSNames:              DNSs,
		IPAddresses:           IPAddresses,
		PublicKeyAlgorithm:    x509.ECDSA,
		PublicKey:             &Private_Key.PublicKey,
	}
	if !CASigned {
		Certificate, err = x509.CreateCertificate(random, &template, &template, &Private_Key.PublicKey, Private_Key)
		if err != nil {
			panic(err)
		}

		Private_Key_Pem, _ = x509.MarshalPKCS8PrivateKey(Private_Key)
	} else {
		x509CaCertificate, _ := x509.ParseCertificate(CaCertificate)

		Certificate, err = x509.CreateCertificate(random, &template, x509CaCertificate, &Private_Key.PublicKey, CAPrivateKey)
		if err != nil {
			panic(err)
		}

		Private_Key_Pem, _ = x509.MarshalPKCS8PrivateKey(Private_Key)
	}

	return Certificate, Private_Key, Private_Key_Pem
}

func ForgeCACertificate(IP string, ca bool, CASigned bool) ([]byte, *ecdsa.PrivateKey, []byte) {

	random := rand.Reader
	var Private_Key_Pem []byte
	var Certificate []byte
	var IPAddresses []net.IP
	var Organizations []string
	var DNSs []string
	var err error

	net_IP := net.ParseIP(IP)

	IPAddresses = append(IPAddresses, net_IP)
	HostName, _ := os.Hostname()

	Organization := string(RandStringBytesMaskImprSrcSB(rand2.Intn(32-8) + 8))
	Organizations = append(Organizations, Organization)
	Private_Key, _ := ecdsa.GenerateKey(elliptic.P521(), random)

	now := time.Now()
	now = now.Add(-1 * 60 * 60 * 24 * 1000 * 1000 * 1000) //yesterday
	then := now.Add(60 * 60 * 24 * 365 * 1000 * 1000 * 1000)

	//fmt.Println(PublicKey.Equal(PrivateKey.Public()))

	DNSs = append(DNSs, "*."+HostName)
	DNSs = append(DNSs, HostName)

	rand2.Seed(time.Now().UTC().UnixNano())

	template := x509.Certificate{
		SerialNumber: big.NewInt(int64(rand2.Intn(math.MaxInt64))),
		Subject: pkix.Name{
			CommonName:   HostName,
			Organization: Organizations,
		},
		NotBefore: now,
		NotAfter:  then,
		//SubjectKeyId:          []byte{1, 2, 3, 4},
		KeyUsage:              x509.KeyUsageCertSign | x509.KeyUsageKeyEncipherment | x509.KeyUsageDigitalSignature,
		BasicConstraintsValid: true,
		IsCA:                  ca,
		DNSNames:              DNSs,
		IPAddresses:           IPAddresses,
		PublicKeyAlgorithm:    x509.ECDSA,
		PublicKey:             &Private_Key.PublicKey,
	}

	Certificate, err = x509.CreateCertificate(random, &template, &template, &Private_Key.PublicKey, Private_Key)
	if err != nil {
		panic(err)
	}

	Private_Key_Pem, _ = x509.MarshalPKCS8PrivateKey(Private_Key)

	return Certificate, Private_Key, Private_Key_Pem
}

//func tarpit(network, address string, c syscall.RawConn) error {
//	return c.Control(func(fd uintptr) {
//		// set the socket options
//		err := syscall.SetsockoptInt(syscall.Handle(fd), syscall.IPPROTO_TCP, syscall.TCP_MAXWIN, 64)
//		if err != nil {
//			log.Println("setsocketopt: ", err)
//		}
//	})
//}

//func AdjustTTL(network, address string, c syscall.RawConn) error {
//	return c.Control(func(fd uintptr) {
//		// set the socket options
//		err := syscall.SetsockoptInt(syscall.Handle(fd), syscall.IPPROTO_IP, syscall.IP_TTL, 64)
//		if err != nil {
//			log.Println("setsocketopt: ", err)
//		}
//	})
//}

func StartSSLServer(ip string) {

	CaCertificate, CAPrivateKey, _ := ForgeCACertificate(ip, true, false) //Self-Signed CA

	Certificate, _, Private_Key_Pem_bytes := ForgeCertificate(ip, false, true, CaCertificate, CAPrivateKey) //CA Signed Certificate

	//x509CaCertificate, err := x509.ParseCertificate(CaCertificate)

	x509Certificate, err := x509.ParseCertificate(Certificate)
	if err != nil {
		panic(err)
	}

	x509CaCertificate, err := x509.ParseCertificate(CaCertificate)
	if err != nil {
		panic(err)
	}

	var Certificate_Pem pem.Block
	Certificate_Pem.Type = "CERTIFICATE"
	Certificate_Pem.Bytes = x509Certificate.Raw

	var Private_Key_Pem pem.Block
	Private_Key_Pem.Type = "PRIVATE KEY"
	Private_Key_Pem.Bytes = Private_Key_Pem_bytes

	//fmt.Println(string(pem.EncodeToMemory(&Private_Key_Pem)))

	tls_Certificate, err := tls.X509KeyPair(pem.EncodeToMemory(&Certificate_Pem), pem.EncodeToMemory(&Private_Key_Pem))
	if err != nil {
		panic(err)
	}

	tls_Certificate.Leaf = x509Certificate
	//tls_Certificate.PrivateKey = PrivateKey ////HERE

	//fmt.Println(PrivateKey)

	Configuration := tls.Config{}
	Configuration.Certificates = append(Configuration.Certificates, tls_Certificate)
	Configuration.MinVersion = tls.VersionTLS12
	Configuration.MaxVersion = tls.VersionTLS13
	//AllowedCiphers := []uint16{tls.TLS_CHACHA20_POLY1305_SHA256}
	//Configuration.CipherSuites = AllowedCiphers
	Configuration.ClientAuth = tls.NoClientCert //RequireAndVerifyClientCert
	//Configuration.InsecureSkipVerify = true     ////TODO REMOVE  THIS!--->TESTING PURPOSE ONLY.
	//Configuration.VerifyConnection = nil
	//Configuration.VerifyPeerCertificate = nil
	listen_port, _ := GetFreePort("0")

	lport_int, _ := strconv.Atoi(listen_port)

	var laddr net.TCPAddr

	laddr.IP = net.ParseIP("0.0.0.0") //outside.
	laddr.Port = lport_int + 1

	//laddr.Zone = ""

	tcp_listen, err := net.ListenTCP("tcp", &laddr)
	if err != nil {
		panic(err)
	}
	fmt.Println("Server listening on port:", listen_port)
	TCP_Conn, err := tcp_listen.AcceptTCP()
	if err != nil {
		panic(err)
	}

	PutRootCA(TCP_Conn, CaCertificate)

	Client_CA := FetchRootCA(TCP_Conn)

	f, err := os.Create("ClientCA.crt")
	if err != nil {
		panic(err)
	}
	f.Write(Client_CA)
	f.Close()

	//TCP_Conn.Close()

	//time.Sleep(time.Millisecond * 1000) ///TODO...DROP this on the internet.

	//x509ClientCaCertificate, err := x509.ParseCertificate(Client_CA)
	//if err != nil {
	//	panic(err)
	//}

	roots := x509.NewCertPool()
	//roots.AddCert(x509CaCertificate)
	//roots.AddCert(x509ClientCaCertificate) //Client's
	roots.AddCert(x509CaCertificate) //Server's

	//Configuration.ClientCAs = roots
	Configuration.RootCAs = roots

	SSL_listen, err := tls.Listen("tcp", "0.0.0.0:"+listen_port, &Configuration)
	if err != nil {
		panic(err)
	}
	net_Conn, err := SSL_listen.Accept()
	if err != nil {
		panic(err)
	}

	////////////////////////TARPIT
	////////////////////////Rate limiting.
	////////////////////////SetNoDelay

	Configuration.ServerName = x509CaCertificate.Subject.CommonName

	tls_Conn := tls.Server(net_Conn, &Configuration)

	/*_ = &tls.Config{
		// Require client certificates (or VerifyConnection will run anyway and
		// panic accessing cs.PeerCertificates[0]) but don't verify them with the
		// default verifier. This will not disable VerifyConnection.
		ClientAuth: tls.RequireAnyClientCert,
		VerifyConnection: func(cs tls.ConnectionState) error {
			opts := x509.VerifyOptions{
				DNSName:       cs.ServerName,
				Intermediates: x509.NewCertPool(),
				KeyUsages:     []x509.ExtKeyUsage{x509.ExtKeyUsageClientAuth},
			}
			for _, cert := range cs.PeerCertificates[1:] {
				opts.Intermediates.AddCert(cert)
			}
			_, err := cs.PeerCertificates[0].Verify(opts)
			return err
		},
	}
	*/
	err = tls_Conn.SetDeadline(time.Now().Add(time.Minute)) //minute and a half
	if err != nil {
		panic(err)
	}
	//if err != nil {
	//	panic(err)
	//}
	//ConnectionState := tls_Conn.ConnectionState()
	//ConnectionState.
	//		Configuration.VerifyConnection(ConnectionState)
	//time.Sleep(time.Millisecond * 1000)
	//

	//bfile := make([]byte, 60000)
	var file []byte
	//n, err := net_Conn.Read(file)
	//if err != nil {
	//	panic(err)
	//}

	err = tls_Conn.Handshake()
	if err != nil {
		panic(err)
	}

	_, err = tls_Conn.Read(file) ///HERE
	if err != nil {
		panic(err)
	}
	//	if err != nil {
	//		if err == io.EOF {
	//			break
	//		} else {
	//			panic(err)
	//		}
	//	}
	//	file = append(file, bfile[:n]...)
	//	fmt.Println("passes")
	//}

	//fmt.Println(n, n2)
	fmt.Println("File received!")

	Checksum := md5.New()
	//Checksum.Write(file)

	//fmt.Println(file)

	_, MP3DiffFileName := ReadDB(hex.EncodeToString(Checksum.Sum(nil)))

	fmt.Println(MP3DiffFileName)

	//NbEntriesDiffFile := "||DIFF||" + strings.Split(MP3DiffFileName, "||")[2]

	//fmt.Println("----->", len([]byte(NbEntriesDiffFile)))

	temp_file, err := os.Create(MP3DiffFileName)
	if err != nil {
		panic(err)
	}

	g := io.Writer(temp_file)

	err = binary.Write(g, binary.LittleEndian, ReadDiffFile(MP3DiffFileName))
	if err != nil {
		panic(err)
	}

	temp_file.Close()

	Data, err := os.ReadFile(MP3DiffFileName)
	if err != nil {
		panic(err)
	}
	Erase(MP3DiffFileName)

	_, err = tls_Conn.Write(Data)

	//DiffFile := md5.New() //set to compare later.
	//DiffFile.Write(Data)

	//fmt.Println("Data--->", len(Data))
	/*
		NumPackets := (len(Data) / last_payload_size) + 1
		Data2 := NumPackets * last_payload_size
		Remainder := last_payload_size - (Data2 - len(Data))

		Downloaded_File := []byte{}

		for i := 0; i < NumPackets; i++ {
			//fmt.Println(Data2)'
			//fmt.Println(i)
			Data2 = Data2 - last_payload_size
			if Data2 > 0 {
				SSL_packet := Data[i*last_payload_size : (i*last_payload_size)+last_payload_size]
				//fmt.Println(i*8192, "<--->", (i*8192)+8192)
				Downloaded_File = append(Downloaded_File, SSL_packet...)
				_, err := tls_Conn.Write(SSL_packet)
				if err != nil {
					panic(err)
				}
			} else { //last packet
				SSL_packet = Data[i*last_payload_size : i*last_payload_size+Remainder]
				Downloaded_File = append(Downloaded_File, SSL_packet...)
				//fmt.Println(i*8192, "<--->", i*8192+Remainder)
				_, err := tls_Conn.Write(SSL_packet)
				if err != nil {
					panic(err)
				}
				SSL_packet = append(SSL_packet, []byte(NbEntriesDiffFile)...) //filename infos
				time.Sleep(time.Millisecond * 10)
				_, err = tls_Conn.Write(SSL_packet)
				if err != nil {
					panic(err)
				}

			}
			time.Sleep(time.Millisecond * 10)
		}
		Downloaded := md5.New()
		Downloaded.Write(Downloaded_File)

		if strings.Compare(hex.EncodeToString(DiffFile.Sum(nil)), hex.EncodeToString(Downloaded.Sum(nil))) == 0 {
			fmt.Println(hex.EncodeToString(Checksum.Sum(nil)), "-->File sent Successfully!")
		}
	*/
	tls_Conn.Close()

}

// //////////////////UDP---Listener---Server---client----START
func createUDPListener() (c *net.UDPConn, close func()) {
	ip, err := net.ResolveUDPAddr("udp4", ":0")
	if err != nil {
		fmt.Println(err)
	}

	c, err = net.ListenUDP("udp4", ip)
	if err != nil {
		panic(err)
	}
	return c, func() {
		_ = c.Close()
	}
}
func StartUDPServer() {
	var Uploaded_File []byte
	var Client_IP *net.UDPAddr
	var Data []byte
	var UDP_packet []byte

	Connection, close := createUDPListener()
	defer close()
	fmt.Println("Listening on:", Connection.LocalAddr())
	buffer := make([]byte, 8192)
	for {
		n, addr, err := Connection.ReadFromUDP(buffer)
		if err != nil {
			panic(err)
		}
		if n < 8192 {
			buffer = buffer[:n]
			Uploaded_File = append(Uploaded_File, buffer...)
			Client_IP = addr
			break
		}

		Uploaded_File = append(Uploaded_File, buffer...)
	}

	Checksum := md5.New()
	Checksum.Write(Uploaded_File)

	_, MP3DiffFileName := ReadDB(hex.EncodeToString(Checksum.Sum(nil)))

	//fmt.Println(MP3DiffFileName)

	NbEntriesDiffFile := "||DIFF||" + strings.Split(MP3DiffFileName, "||")[2]

	//fmt.Println("----->", len([]byte(NbEntriesDiffFile)))

	temp_file, err := os.Create(MP3DiffFileName)
	if err != nil {
		panic(err)
	}

	g := io.Writer(temp_file)

	err = binary.Write(g, binary.LittleEndian, ReadDiffFile(MP3DiffFileName))
	if err != nil {
		panic(err)
	}

	temp_file.Close()

	Data, err = os.ReadFile(MP3DiffFileName)
	if err != nil {
		panic(err)
	}
	Erase(MP3DiffFileName)

	DiffFile := md5.New() //set to compare later.
	DiffFile.Write(Data)

	//fmt.Println("Data--->", len(Data))

	NumPackets := (len(Data) / 8192) + 1
	Data2 := NumPackets * 8192
	Remainder := 8192 - (Data2 - len(Data))

	Downloaded_File := []byte{}

	for i := 0; i < NumPackets; i++ {
		//fmt.Println(Data2)'
		//fmt.Println(i)
		Data2 = Data2 - 8192
		if Data2 > 0 {
			UDP_packet = Data[i*8192 : (i*8192)+8192]
			//fmt.Println(i*8192, "<--->", (i*8192)+8192)
			Downloaded_File = append(Downloaded_File, UDP_packet...)
			_, err := Connection.WriteToUDP(UDP_packet, Client_IP)
			if err != nil {
				panic(err)
			}
		} else { //last packet
			UDP_packet = Data[i*8192 : i*8192+Remainder]
			Downloaded_File = append(Downloaded_File, UDP_packet...)
			//fmt.Println(i*8192, "<--->", i*8192+Remainder)
			_, err := Connection.WriteToUDP(UDP_packet, Client_IP)
			if err != nil {
				panic(err)
			}
			UDP_packet = append(UDP_packet, []byte(NbEntriesDiffFile)...) //filename infos
			time.Sleep(time.Millisecond * 10)
			_, err = Connection.WriteToUDP(UDP_packet, Client_IP)
			if err != nil {
				panic(err)
			}

		}
		time.Sleep(time.Millisecond * 10)
	}
	Downloaded := md5.New()
	Downloaded.Write(Downloaded_File)

	if strings.Compare(hex.EncodeToString(DiffFile.Sum(nil)), hex.EncodeToString(Downloaded.Sum(nil))) == 0 {
		fmt.Println(hex.EncodeToString(Checksum.Sum(nil)), "-->File sent Successfully!")
	}

}

func StartUDPClient(Mp3_Modded string, ip string, port string) {
	var UDP_packet []byte
	var Uploaded_File []byte
	var Client_IP net.Addr
	var NbEntriesDiffFile string
	ConnectInfos := ip + ":" + port
	fmt.Println("Establishing a connection with ", ConnectInfos)
	Server, err := net.ResolveUDPAddr("udp4", ConnectInfos)
	if err != nil {
		panic(err)
	}
	Connection, err := net.DialUDP("udp4", nil, Server)
	if err != nil {
		panic(err)
	}
	defer Connection.Close()

	MP3_Bytes, err := os.ReadFile(Mp3_Modded)
	if err != nil {
		panic(err)
	}
	fmt.Println("Sending...", Mp3_Modded)

	NumPackets := (len(MP3_Bytes) / 8192) + 1
	Data2 := NumPackets * 8192
	Remainder := 8192 - (Data2 - len(MP3_Bytes))

	for i := 0; i < NumPackets; i++ {
		//fmt.Println(Data2)'
		//fmt.Println(i)
		Data2 = Data2 - 8192
		if Data2 > 0 {
			UDP_packet = MP3_Bytes[i*8192 : (i*8192)+8192]
			//fmt.Println(i*8192, "<--->", (i*8192)+8192)
			_, err := Connection.Write(UDP_packet)
			if err != nil {
				panic(err)
			}
		} else { //last packet
			UDP_packet = MP3_Bytes[i*8192 : i*8192+Remainder]
			//fmt.Println(i*8192, "<--->", i*8192+Remainder)
			_, err := Connection.Write(UDP_packet)
			if err != nil {
				panic(err)
			}

		}
		time.Sleep(time.Millisecond * 10)
	}
	fmt.Println("Receiving...")
	buffer := make([]byte, 8192)
	buffer2 := make([]byte, 8192)
	for {
		n, _, err := Connection.ReadFrom(buffer)
		if err != nil {
			panic(err)
		}
		if n < 8192 {
			buffer = buffer[:n]
			Uploaded_File = append(Uploaded_File, buffer...)
			n, addr, err := Connection.ReadFrom(buffer2)
			buffer2 = buffer2[:n]
			Client_IP = addr
			//fmt.Println(string(buffer2))
			NbEntriesDiffFile = strings.Split(string(buffer2), "||DIFF||")[1]
			if err != nil {
				panic(err)
			}
			break
		}

		Uploaded_File = append(Uploaded_File, buffer...)
	}

	fmt.Println("Receving Database from...", Client_IP.String())

	if _, err := os.Stat("DATABASE"); os.IsNotExist(err) {
		err := os.Mkdir("DATABASE", os.ModePerm)
		if err != nil {
			panic(err)
		}
	}

	Downloaded := md5.New()
	Downloaded.Write(MP3_Bytes)

	fmt.Println("Writing DATABASE ...")

	f, err := os.Create(hex.EncodeToString(Downloaded.Sum(nil)) + "||DIFF||" + NbEntriesDiffFile) //for test purposes
	if err != nil {
		panic(err)
	}

	f.Write(Uploaded_File)

	f.Close()

}

////////////////////UDP---Listener---Server---client----END

func permutations(arr []string) [][]string {
	var helper func([]string, int)
	res := [][]string{}

	helper = func(arr []string, n int) {
		if n == 1 {
			tmp := make([]string, len(arr))
			copy(tmp, arr)
			res = append(res, tmp)
		} else {
			for i := 0; i < n; i++ {
				helper(arr, n-1)
				if n%2 == 1 {
					tmp := arr[i]
					arr[i] = arr[n-1]
					arr[n-1] = tmp
				} else {
					tmp := arr[0]
					arr[0] = arr[n-1]
					arr[n-1] = tmp
				}
			}
		}
	}
	helper(arr, len(arr))
	return res
}

var stringToShape = map[string]Shape{
	"sine":     0,
	"square":   1,
	"downsaw":  2,
	"upsaw":    3,
	"triangle": 4,
}

type Database struct {
	md5Sum         string
	BandpassFilter []float64
	MissingBits    []float64
}

func main() {
	var Arguments []string
	Arguments = append(Arguments, os.Args[1:]...)

	var Entries []Database
	//var recovered_modded [][]byte
	var OperationsTypes []string
	var WaveStruct Wave

	stat, _ := os.Stdin.Stat()

	if (stat.Mode() & os.ModeCharDevice) == 0 {

		data, _ := io.ReadAll(os.Stdin)

		os.Stdout.Write(data[:len(data)-1])

	} else {
		ValidChoices, err := ValidateArguments(Arguments)
		if err != nil {
			fmt.Println(err)
			DisplayUsage()
		}
		WitchCraft, Spells := ParseArguments(ValidChoices, Arguments)

		if err == nil {

			file_index := "00000000000000000000"
			filename := file_index + ".wav"
			initialized, _ := strconv.Atoi(file_index)
			initialized++
			initialized_wave := strconv.Itoa(initialized) + ".wav"
			duration := 1
			frequency := 48000 //Hertz
			bits := 16         //16 bits PCM

			OriginalWav := WitchCraft["OriginalWav"]
			OriginalData := WitchCraft["OriginalData"]
			Modded := "MODDED-" + file_index + ".wav"
			Modded_MP3 := WitchCraft["Modded_MP3"]
			Wav_OutFile := "MODDED-OUTFILE.wav"
			Diff_Recovered := "DIFF-RECOVERED.wav"

			if OriginalWav != "" { //use what the user provided for input WAVE file.
				initialized_wave = strings.Split(OriginalWav, ".")[0] + "-Initialized.wav"
				WaveStruct, err = ReadWaveFile(OriginalWav)
				if err != nil {
					panic(err)
				}
				InitializeWav(OriginalWav, initialized_wave, WaveStruct.SampleRate, WaveStruct.NumChannels)

			} else { //generate an input WAVE file.
				if OriginalData != "" {
					wfmt := generate_file(filename, frequency, bits, duration, stringToShape[("sine")])

					File1sInfos, _ := os.Stat(filename)
					sFileSize := File1sInfos.Size()
					OriginalDataFileInfos, err := os.Stat(OriginalData)
					if err != nil {
						panic(err)
					}
					OriginalDataFileSize := OriginalDataFileInfos.Size()

					duration = int(OriginalDataFileSize)/int(sFileSize) + 1 //extra second just in case.

					wfmt = generate_file(filename, frequency, bits, duration, stringToShape[("sine")])
					InitializeWav(filename, initialized_wave, wfmt.SampleRate, wfmt.NumChannels)
					Erase(filename)
					WaveStruct, err = ReadWaveFile(initialized_wave)
					if err != nil {
						panic(err)
					}
				}
			}
			//fmt.Println(Spells)
			//os.Exit(0)
			for _, Spell := range Spells {
				switch strings.Split(Spell, " ")[0] {
				case "-w": //Input WAVE file
					OperationsTypes = append(OperationsTypes, "w")
				case "-o": //Ouput MP3 filename - Used in Client mode
					OperationsTypes = append(OperationsTypes, "o")
				case "-h": //File to conceal
					OperationsTypes = append(OperationsTypes, "h")
				case "-s": //Server - Listen mode
					//fmt.Println(Spell)
					if len(strings.Split(Spell, " ")) > 1 {
						OperationsTypes = append(OperationsTypes, "ss")
					} else {
						OperationsTypes = append(OperationsTypes, "s")
					}
				case "-ip": //Client - Connect
					OperationsTypes = append(OperationsTypes, "i")
				case "-p": //Client - Connect - Port
					OperationsTypes = append(OperationsTypes, "p")
				case "-ssl": //Client - Connect - TLS
					OperationsTypes = append(OperationsTypes, "s")
				case "-r": //Recover file
					OperationsTypes = append(OperationsTypes, "r")
				}
			}
			//////---PERMUTATIONS----ALGO---len 4
			//var Casts []string
			//var Cast_Line string
			//if len(OperationsTypes) == 4 {
			//	Perms := permutations(OperationsTypes)
			//	for _, Perm := range Perms {
			//		Casts = append(Casts, strings.Join(Perm, ""))
			//	}
			//fmt.Println(Cast)
			//	for _, Cast := range Casts {
			//		Cast_Line = Cast_Line + "," + "'" + Cast + "'"
			//	}
			//	Cast_Line = Cast_Line[1:]
			//	fmt.Println(Cast_Line)
			//}
			switch strings.Join(OperationsTypes, "") {
			case "w":
				DisplayUsage()
			case "wh":
				Modded_MP3 = strings.Split(OriginalData, ".")[0] + "-Hidden.mp3"
				WaveStruct, err = ReadWaveFile(OriginalWav)
				if err != nil {
					panic(err)
				}
				InitializeWav(OriginalWav, initialized_wave, WaveStruct.SampleRate, WaveStruct.NumChannels)
				Entries = ReadWrite(initialized_wave, OriginalData, Modded, Modded_MP3, Wav_OutFile, Diff_Recovered, Entries)
				Erase(initialized_wave)
				Erase(Modded)
				Erase(Wav_OutFile)
				Erase(Diff_Recovered)
			case "hw":
				Modded_MP3 = strings.Split(OriginalData, ".")[0] + "-Hidden.mp3"
				WaveStruct, err = ReadWaveFile(OriginalWav)
				if err != nil {
					panic(err)
				}
				InitializeWav(OriginalWav, initialized_wave, WaveStruct.SampleRate, WaveStruct.NumChannels)
				Entries = ReadWrite(initialized_wave, OriginalData, Modded, Modded_MP3, Wav_OutFile, Diff_Recovered, Entries)
				Erase(initialized_wave)
				Erase(Modded)
				Erase(Wav_OutFile)
				Erase(Diff_Recovered)
			case "woh":
				Modded_MP3 = strings.Split(OriginalData, ".")[0] + "-Hidden.mp3"
				WaveStruct, err = ReadWaveFile(OriginalWav)
				if err != nil {
					panic(err)
				}
				InitializeWav(OriginalWav, initialized_wave, WaveStruct.SampleRate, WaveStruct.NumChannels)
				Entries = ReadWrite(initialized_wave, OriginalData, Modded, Modded_MP3, Wav_OutFile, Diff_Recovered, Entries)
				Erase(initialized_wave)
				Erase(Modded)
				Erase(Wav_OutFile)
				Erase(Diff_Recovered)
			case "hwo":
				Modded_MP3 = strings.Split(OriginalData, ".")[0] + "-Hidden.mp3"
				WaveStruct, err = ReadWaveFile(OriginalWav)
				if err != nil {
					panic(err)
				}
				InitializeWav(OriginalWav, initialized_wave, WaveStruct.SampleRate, WaveStruct.NumChannels)
				Entries = ReadWrite(initialized_wave, OriginalData, Modded, Modded_MP3, Wav_OutFile, Diff_Recovered, Entries)
				Erase(initialized_wave)
				Erase(Modded)
				Erase(Wav_OutFile)
				Erase(Diff_Recovered)
			case "ohw":
				Modded_MP3 = strings.Split(OriginalData, ".")[0] + "-Hidden.mp3"
				WaveStruct, err = ReadWaveFile(OriginalWav)
				if err != nil {
					panic(err)
				}
				InitializeWav(OriginalWav, initialized_wave, WaveStruct.SampleRate, WaveStruct.NumChannels)
				Entries = ReadWrite(initialized_wave, OriginalData, Modded, Modded_MP3, Wav_OutFile, Diff_Recovered, Entries)
				Erase(initialized_wave)
				Erase(Modded)
				Erase(Wav_OutFile)
				Erase(Diff_Recovered)
			case "owh":
				Modded_MP3 = strings.Split(OriginalData, ".")[0] + "-Hidden.mp3"
				WaveStruct, err = ReadWaveFile(OriginalWav)
				if err != nil {
					panic(err)
				}
				InitializeWav(OriginalWav, initialized_wave, WaveStruct.SampleRate, WaveStruct.NumChannels)
				Entries = ReadWrite(initialized_wave, OriginalData, Modded, Modded_MP3, Wav_OutFile, Diff_Recovered, Entries)
				Erase(initialized_wave)
				Erase(Modded)
				Erase(Wav_OutFile)
				Erase(Diff_Recovered)
			case "how":
				Modded_MP3 = strings.Split(OriginalData, ".")[0] + "-Hidden.mp3"
				WaveStruct, err = ReadWaveFile(OriginalWav)
				if err != nil {
					panic(err)
				}
				InitializeWav(OriginalWav, initialized_wave, WaveStruct.SampleRate, WaveStruct.NumChannels)
				Entries = ReadWrite(initialized_wave, OriginalData, Modded, Modded_MP3, Wav_OutFile, Diff_Recovered, Entries)
				Erase(initialized_wave)
				Erase(Modded)
				Erase(Wav_OutFile)
				Erase(Diff_Recovered)
			case "who":
				Modded_MP3 = strings.Split(OriginalData, ".")[0] + "-Hidden.mp3"
				WaveStruct, err = ReadWaveFile(OriginalWav)
				if err != nil {
					panic(err)
				}
				InitializeWav(OriginalWav, initialized_wave, WaveStruct.SampleRate, WaveStruct.NumChannels)
				Entries = ReadWrite(initialized_wave, OriginalData, Modded, Modded_MP3, Wav_OutFile, Diff_Recovered, Entries)
				Erase(initialized_wave)
				Erase(Modded)
				Erase(Wav_OutFile)
				Erase(Diff_Recovered)
			case "oh":
				Modded_MP3 = strings.Split(OriginalData, ".")[0] + "-Hidden.mp3"
				WaveStruct, err = ReadWaveFile(OriginalWav)
				if err != nil {
					panic(err)
				}
				InitializeWav(OriginalWav, initialized_wave, WaveStruct.SampleRate, WaveStruct.NumChannels)
				Entries = ReadWrite(initialized_wave, OriginalData, Modded, Modded_MP3, Wav_OutFile, Diff_Recovered, Entries)
				Erase(initialized_wave)
				Erase(Modded)
				Erase(Wav_OutFile)
				Erase(Diff_Recovered)
			case "ho":
				Modded_MP3 = strings.Split(OriginalData, ".")[0] + "-Hidden.mp3"
				WaveStruct, err = ReadWaveFile(OriginalWav)
				if err != nil {
					panic(err)
				}
				InitializeWav(OriginalWav, initialized_wave, WaveStruct.SampleRate, WaveStruct.NumChannels)
				Entries = ReadWrite(initialized_wave, OriginalData, Modded, Modded_MP3, Wav_OutFile, Diff_Recovered, Entries)
				Erase(initialized_wave)
				Erase(Modded)
				Erase(Wav_OutFile)
				Erase(Diff_Recovered)
			case "h":
				Modded_MP3 = strings.Split(OriginalData, ".")[0] + "-Hidden.mp3"
				Entries = ReadWrite(initialized_wave, OriginalData, Modded, Modded_MP3, Wav_OutFile, Diff_Recovered, Entries)
				Erase(initialized_wave)
				Erase(Modded)
				Erase(Wav_OutFile)
				Erase(Diff_Recovered)
			case "s":
				StartUDPServer()
			case "ss":
				//IP := strings.Split(WitchCraft["IP"], ";")[0]
				External_IP := WitchCraft["IP"]
				//KeyFile := strings.Split(WitchCraft["ssl"], ";")[1]
				//fmt.Println(IP)
				StartSSLServer(External_IP)
			case "oip":
				Modded_MP3 := WitchCraft["Modded_MP3"]
				ip := WitchCraft["ip"]
				port := WitchCraft["port"]
				StartUDPClient(Modded_MP3, ip, port)
			case "poi":
				Modded_MP3 := WitchCraft["Modded_MP3"]
				ip := WitchCraft["ip"]
				port := WitchCraft["port"]
				StartUDPClient(Modded_MP3, ip, port)
			case "ipo":
				Modded_MP3 := WitchCraft["Modded_MP3"]
				ip := WitchCraft["ip"]
				port := WitchCraft["port"]
				StartUDPClient(Modded_MP3, ip, port)
			case "iop":
				Modded_MP3 := WitchCraft["Modded_MP3"]
				ip := WitchCraft["ip"]
				port := WitchCraft["port"]
				StartUDPClient(Modded_MP3, ip, port)
			case "pio":
				Modded_MP3 := WitchCraft["Modded_MP3"]
				ip := WitchCraft["ip"]
				port := WitchCraft["port"]
				StartUDPClient(Modded_MP3, ip, port)
			case "opi":
				Modded_MP3 := WitchCraft["Modded_MP3"]
				ip := WitchCraft["ip"]
				port := WitchCraft["port"]
				StartUDPClient(Modded_MP3, ip, port)
			case "pi":
				DisplayUsage()
			case "ip":
				DisplayUsage()
			case "oips", "iops", "pios", "ipos", "pois", "opis", "soip", "osip", "iosp", "oisp", "isop", "siop", "psoi", "spoi", "ospi", "sopi", "opsi", "posi", "ipso", "piso", "spio", "psio", "sipo", "ispo":
				//fmt.Println("Casted")
				Modded_MP3 := WitchCraft["Modded_MP3"]
				ip := WitchCraft["ip"]
				port := WitchCraft["port"]
				External_IP := WitchCraft["IP"]
				//CertFile := strings.Split(WitchCraft["ssl"], ";")[0]
				//KeyFile := strings.Split(WitchCraft["ssl"], ";")[1]
				StartSSLClient(Modded_MP3, ip, port, External_IP) //, CertFile, KeyFile)
			case "r":
				recovered_modded, _ := GoHunting(OriginalWav, OriginalData, Modded, Modded_MP3, Wav_OutFile, Diff_Recovered, Entries)
				WaveStruct, err = ReadWaveFile(Wav_OutFile)
				if err != nil {
					panic(err)
				}
				Recover(Modded_MP3, recovered_modded, WaveStruct)
				Erase(Diff_Recovered)
				Erase(Wav_OutFile)
			}
		}
	}
}

func ParseArguments(ValidChoices []string, Arguments []string) (map[string]string, map[string]string) {
	Switches := make(map[string]string)
	Operators := make(map[string]string, len(ValidChoices))
	i := 0

	for _, Choice := range ValidChoices {
		for _, Argument := range Arguments {
			if Choice == Argument {
				if len(Arguments) > 1 {
					if Choice != "-s" && Choice != "-ssl" {
						Operators[Choice] = Arguments[i] + " " + Arguments[i+1] //Grab the parameter for the Argument
					} else {
						if Choice == "-s" {
							for j := 0; j < len(Arguments); j++ {
								if Arguments[j] == "-ssl" { // -s -ssl [IP]
									Operators[Choice] = Arguments[i] + " " + Arguments[j+1] //+ " " + Arguments[j+1] //+ " " + Arguments[j+2] //certificate and private key
									i++
									break
								}
							}
						} else {
							if Choice == "-ssl" && Operators["-s"] == "" {
								Operators[Choice] = Arguments[i] + " " + Arguments[i+1] //+ " " + Arguments[i+2]
								//		i++
							}
						}
					}
				} else {
					Operators[Choice] = Arguments[i] + " " + " "
				}

			}
		}
		i = i + 2
	}

	for _, Operator := range Operators {
		switch strings.Split(Operator, " ")[0] {
		case "-w": //Input WAVE file
			Switches["OriginalWav"] = strings.Split(Operator, " ")[1]
		case "-o": //Ouput MP3 filename - testing purposes - hidden feature
			Switches["Modded_MP3"] = strings.Split(Operator, " ")[1]
		case "-h": //File to conceal
			Switches["OriginalData"] = strings.Split(Operator, " ")[1]
		case "-s": //Server - Listen mode
			Switches["ServerMode"] = "true"
			if len(strings.Split(Operator, " ")[0]) > 1 {
				Switches["IP"] = strings.Split(Operator, " ")[1] // + ";" + strings.Split(Operators["-s"], " ")[3] // crt_file;key_file
			}
		case "-ip": //Client - Connect
			Switches["ip"] = strings.Split(Operator, " ")[1]
		case "-p": //Client - Connect - Port
			Switches["port"] = strings.Split(Operator, " ")[1]
		case "-ssl": //Client - Connect - TLS
			if Switches["ServerMode"] == "" {
				Switches["IP"] = strings.Split(Operator, " ")[1] //strings.Split(Operator, " ")[1] //+ ";" + strings.Split(Operators["-ssl"], " ")[2] // crt_file;key_file
			}
		case "-r": //recover file
			Switches["Modded_MP3"] = strings.Split(Operator, " ")[1]
		}
	}
	return Switches, Operators
}

func ValidateArguments(Arguments []string) ([]string, error) {
	const OK = true
	var Pass bool
	var valid []string

	for _, Argument := range Arguments {
		switch Argument {
		case "-w": //Input WAVE file
			fmt.Print(".")
			valid = append(valid, Argument)
		case "-o": //Ouput MP3 filename - testing purposes - hidden feature
			fmt.Print(".")
			valid = append(valid, Argument)
		case "-h": //File to conceal
			fmt.Print(".")
			valid = append(valid, Argument)
		case "-s": //Server - Listen mode
			fmt.Print(".")
			valid = append(valid, Argument)
		case "-ip": //Client - Connect
			fmt.Print(".")
			valid = append(valid, Argument)
		case "-p": //Client - Connect - Port
			fmt.Print(".")
			valid = append(valid, Argument)
		case "-ssl": //Client - Connect - TLS
			fmt.Print(".")
			valid = append(valid, Argument)
		case "-r": //Recover Stegged Document
			fmt.Print(".")
			valid = append(valid, Argument)
		default:
			Pass = OK
		}
	}
	if Pass || len(valid) > 0 {
		return valid, nil
	} else {
		return valid, errors.New("arguments invalid")
	}
}

func DisplayUsage() {
	fmt.Println("-== WAV2GO ==-")
	fmt.Println("WAV2GO: depends on ffmpeg binaries...")
	fmt.Println("WAV2GO: -w [Original Wave filename] -h [File to Conceal] -o [Destination MP3]")
	fmt.Println("WAV2GO: -r [MP3 Stegged filename] ... recover file")
	fmt.Println("WAV2GO: -s ... DB server mode")
	fmt.Println("WAV2GO: -s -ssl [External IP Address] ... DB server SSL mode")
	fmt.Println("WAV2GO: -o [MP3 file to recover] -ip [Server's IP address] -port [Server's Port] ... DB Client mode[UDP]")
	fmt.Println("WAV2GO: -o [MP3 file to recover] -ip [Server's IP address] -port [Server's Port] -ssl [External IP address]... DB ssl/tls client mode[TCP]")
}
