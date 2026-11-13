const FIRE_NAMES = ["Palisades", "Eaton"];
const FIRE_COLORS = { Palisades: "#e8743b", Eaton: "#3b6fd8", Other: "#9a9a9a" };
const WIND_COLOR = "#087e9c";
const WIND_STREAM_COLOR = "#ffffff";
const MAP_REGION = { west: -118.95, east: -117.85, south: 33.85, north: 34.45 };
const PACIFIC_OFFSET_MS = 8 * 60 * 60 * 1000;
const SCAN_STEP_MS = 5 * 60 * 1000;
const HOUR_MS = 60 * 60 * 1000;
const ALIGNED_STEP_HOURS = 1 / 12;
const PLAY_INTERVAL_MS = 80;
const LOW_WIND_PRESSURE_HPA = 700;
const WIND_FIELD_RADIUS = 175;
const WIND_BACKGROUND_BLEND = 0.18;
const WIND_STREAM_SPACING = 40;
const WIND_STREAM_STEP = 3;
const WIND_STREAM_STEPS = 48;

const mapWidth = 760;
const mapHeight = 470;
const chartWidth = 1000;
const powerChartHeight = 220;
const windChartHeight = 120;
const chartMargin = { top: 16, right: 24, bottom: 32, left: 64 };

const referencePlaces = [
  { name: "Malibu", lon: -118.7798, lat: 34.0259 },
  { name: "Santa Monica", lon: -118.4912, lat: 34.0195 },
  { name: "Downtown LA", lon: -118.2437, lat: 34.0522 },
  { name: "Burbank", lon: -118.3090, lat: 34.1808 },
  { name: "Pasadena", lon: -118.1445, lat: 34.1478 }
];

const state = {
  mode: "clock",
  stepIndex: 0,
  showWind: true,
  lowWindOnly: false,
  playTimer: null
};

let detections;
let pixels;
let fireInfo;
let scanTimes;
let alignedSteps;
let seriesByFire;
let winds;
let hourlyWind;
let projection;
let frpRadius;
let pixelSize;
let chartScales = {};
let mapZoom;
let zoomScale = 1;
let activeTotals = {};
let windStreamCacheKey = null;
let windStreamCache = [];

const formatPacific = d3.utcFormat("%a %b %-d, %-I:%M %p");
const formatPacificHour = d3.utcFormat("%a %-I %p");
const tooltip = d3.select("#tooltip");
const windStreamLine = d3.line()
  .x(point => point.x)
  .y(point => point.y)
  .curve(d3.curveCatmullRom.alpha(0.5));

function toPacific(date) {
  return new Date(date.getTime() - PACIFIC_OFFSET_MS);
}

function describeTime(date) {
  return `${formatPacific(toPacific(date))} PST`;
}

function describeSpeed(metersPerSecond) {
  return `${Math.round(metersPerSecond)} m/s (${Math.round(metersPerSecond * 2.237)} mph)`;
}

function interpolateWindAt(x, y, observations, backgroundWind) {
  let totalWeight = 0;
  let east = 0;
  let north = 0;
  let pressure = 0;
  let nearestDistance = Infinity;
  const radiusSquared = WIND_FIELD_RADIUS ** 2;

  for (const observation of observations) {
    const distanceX = observation.x - x;
    const distanceY = observation.y - y;
    const distanceSquared = distanceX * distanceX + distanceY * distanceY;
    if (distanceSquared > radiusSquared) {
      continue;
    }

    nearestDistance = Math.min(nearestDistance, Math.sqrt(distanceSquared));
    const weight = 1 / (distanceSquared + 36);
    totalWeight += weight;
    east += observation.east * weight;
    north += observation.north * weight;
    pressure += observation.pressure * weight;
  }

  if (totalWeight === 0) {
    return null;
  }

  east /= totalWeight;
  north /= totalWeight;
  east = east * (1 - WIND_BACKGROUND_BLEND) + backgroundWind.east * WIND_BACKGROUND_BLEND;
  north = north * (1 - WIND_BACKGROUND_BLEND) + backgroundWind.north * WIND_BACKGROUND_BLEND;
  return {
    east: east,
    north: north,
    speed: Math.hypot(east, north),
    pressure: pressure / totalWeight,
    nearestDistance: nearestDistance
  };
}

function traceWindSide(startX, startY, observations, backgroundWind, direction) {
  const points = [{ x: startX, y: startY }];
  let x = startX;
  let y = startY;

  for (let stepIndex = 0; stepIndex < WIND_STREAM_STEPS; stepIndex += 1) {
    const currentWind = interpolateWindAt(x, y, observations, backgroundWind);
    if (currentWind === null || currentWind.speed < 0.5) {
      break;
    }

    const speed = currentWind.speed;
    const middleX = x + (currentWind.east / speed) * WIND_STREAM_STEP * direction * 0.5;
    const middleY = y - (currentWind.north / speed) * WIND_STREAM_STEP * direction * 0.5;
    const middleWind = interpolateWindAt(middleX, middleY, observations, backgroundWind);
    if (middleWind === null || middleWind.speed < 0.5) {
      break;
    }

    const nextX = x + (middleWind.east / middleWind.speed) * WIND_STREAM_STEP * direction;
    const nextY = y - (middleWind.north / middleWind.speed) * WIND_STREAM_STEP * direction;
    if (nextX < 0 || nextX > mapWidth || nextY < 0 || nextY > mapHeight) {
      break;
    }

    let loopsBack = false;
    for (let pointIndex = 0; pointIndex < points.length - 4; pointIndex += 1) {
      if (Math.hypot(points[pointIndex].x - nextX, points[pointIndex].y - nextY) < 9) {
        loopsBack = true;
        break;
      }
    }
    if (loopsBack) {
      break;
    }

    x = nextX;
    y = nextY;
    points.push({ x: x, y: y });
  }

  return points;
}

function addStreamlineMeander(points, phase) {
  const amplitude = Math.min(20, points.length * 0.2);
  return points.map((point, index) => {
    const progress = index / (points.length - 1);
    const previous = points[Math.max(0, index - 1)];
    const next = points[Math.min(points.length - 1, index + 1)];
    const tangentX = next.x - previous.x;
    const tangentY = next.y - previous.y;
    const tangentLength = Math.hypot(tangentX, tangentY) || 1;
    const envelope = Math.sin(Math.PI * progress);
    const offset = amplitude * Math.sin((4 * Math.PI * progress) + phase) * envelope;
    return {
      x: point.x - (tangentY / tangentLength) * offset,
      y: point.y + (tangentX / tangentLength) * offset
    };
  });
}

function createWindStreamlines(hourWinds) {
  const levels = state.lowWindOnly
    ? [{ nearGround: true, rows: hourWinds }]
    : [
      { nearGround: false, rows: hourWinds.filter(d => d.pressure < LOW_WIND_PRESSURE_HPA) },
      { nearGround: true, rows: hourWinds.filter(d => d.pressure >= LOW_WIND_PRESSURE_HPA) }
    ];
  const streamlines = [];

  for (const level of levels) {
    const observations = level.rows.map(d => {
      const [x, y] = projection([d.lon, d.lat]);
      return { ...d, x: x, y: y };
    });
    const backgroundWind = {
      east: d3.mean(observations, d => d.east) || 0,
      north: d3.mean(observations, d => d.north) || 0
    };

    for (let y = WIND_STREAM_SPACING / 2; y < mapHeight; y += WIND_STREAM_SPACING) {
      for (let x = WIND_STREAM_SPACING / 2; x < mapWidth; x += WIND_STREAM_SPACING) {
        const seedWind = interpolateWindAt(x, y, observations, backgroundWind);
        if (seedWind === null || seedWind.speed < 0.5) {
          continue;
        }

        const backward = traceWindSide(x, y, observations, backgroundWind, -1).reverse();
        const forward = traceWindSide(x, y, observations, backgroundWind, 1).slice(1);
        const points = backward.concat(forward);
        if (points.length < 5) {
          continue;
        }
        const endsNearEachOther = Math.hypot(
          points[0].x - points[points.length - 1].x,
          points[0].y - points[points.length - 1].y
        ) < 18;
        if (points.length >= 20 && endsNearEachOther) {
          continue;
        }

        streamlines.push({
          id: `${level.nearGround ? "ground" : "aloft"}|${x}|${y}`,
          points: addStreamlineMeander(points, (x * 0.017 + y * 0.013) % (2 * Math.PI)),
          speed: seedWind.speed,
          nearGround: level.nearGround
        });
      }
    }
  }

  return streamlines;
}

function possessive(name) {
  if (name.endsWith("s")) {
    return `${name}'`;
  }
  return `${name}'s`;
}

function fireLabelHtml(fireName) {
  return `<strong style="color: ${FIRE_COLORS[fireName]}">${fireName}</strong>`;
}

function distanceKm(latitude1, longitude1, latitude2, longitude2) {
  const toRadians = Math.PI / 180;
  const phi1 = latitude1 * toRadians;
  const phi2 = latitude2 * toRadians;
  const halfChord = Math.sin((phi2 - phi1) / 2) ** 2 + Math.cos(phi1) * Math.cos(phi2) * Math.sin(((longitude2 - longitude1) * toRadians) / 2) ** 2;
  return 6371 * 2 * Math.asin(Math.sqrt(halfChord));
}

function describeDuration(hours) {
  const wholeHours = Math.floor(hours);
  const minutes = Math.round((hours - wholeHours) * 60);
  if (wholeHours === 0) {
    return `${minutes} min`;
  }
  return `${wholeHours} h ${minutes} min`;
}

function nearestIndex(sortedValues, target) {
  const index = d3.bisector(value => value).center(sortedValues, target);
  return Math.max(0, Math.min(sortedValues.length - 1, index));
}

function currentSteps() {
  if (state.mode === "clock") {
    return scanTimes;
  }
  return alignedSteps;
}

function currentValue() {
  return currentSteps()[state.stepIndex];
}

function fireTimeForValue(fireName, value) {
  if (state.mode === "clock") {
    return value;
  }
  return new Date(fireInfo[fireName].ignition.getTime() + value * HOUR_MS);
}

function pixelIsReached(pixel, value) {
  if (state.mode === "clock") {
    return pixel.firstTime <= value;
  }
  if (FIRE_NAMES.includes(pixel.fire) === false) {
    return false;
  }
  return pixel.firstHours <= value;
}

function detectionIsActive(detection, value) {
  if (state.mode === "clock") {
    const age = value.getTime() - detection.time.getTime();
    return age >= 0 && age < SCAN_STEP_MS;
  }
  if (FIRE_NAMES.includes(detection.fire) === false) {
    return false;
  }
  const ageHours = value - detection.hoursSinceIgnition;
  return ageHours >= 0 && ageHours < ALIGNED_STEP_HOURS;
}

Promise.all([
  d3.csv("data/detections.csv"),
  d3.csv("data/timeseries.csv"),
  d3.csv("data/winds.csv"),
  d3.json("data/meta.json"),
  d3.json("data/socal_counties.geojson")
]).then(([detectionRows, timeseriesRows, windRows, metadata, counties]) => {
  prepareData(detectionRows, timeseriesRows, windRows, metadata);
  drawMap(counties);
  drawKeyMoments();
  drawFindings();
  setUpControls();
  resetForMode();
});

function prepareData(detectionRows, timeseriesRows, windRows, metadata) {
  fireInfo = {};
  for (const fireName of FIRE_NAMES) {
    const fire = metadata.fires[fireName];
    fireInfo[fireName] = {
      ignition: new Date(fire.ignition),
      lat: +fire.lat,
      lon: +fire.lon
    };
  }

  detections = detectionRows.map(row => ({
    time: new Date(row.time),
    fire: row.fire,
    lat: +row.lat,
    lon: +row.lon,
    frp: row.frp === "" ? 0 : +row.frp,
    temp: row.temp === "" ? null : +row.temp,
    pixelKey: `${row.pixel_y}_${row.pixel_x}`,
    hoursSinceIgnition: row.hours_since_ignition === "" ? null : +row.hours_since_ignition
  }));

  pixels = [];
  const detectionsByPixel = d3.group(detections, d => `${d.fire}|${d.pixelKey}`);
  for (const [pixelId, pixelDetections] of detectionsByPixel) {
    const firstDetection = d3.least(pixelDetections, d => d.time);
    pixels.push({
      id: pixelId,
      fire: firstDetection.fire,
      lat: firstDetection.lat,
      lon: firstDetection.lon,
      firstTime: firstDetection.time,
      firstHours: firstDetection.hoursSinceIgnition,
      scanCount: pixelDetections.length,
      peakFrp: d3.max(pixelDetections, d => d.frp)
    });
  }

  const uniqueTimes = Array.from(new Set(timeseriesRows.map(row => row.time))).sort();
  scanTimes = uniqueTimes.map(time => new Date(time));

  seriesByFire = {};
  for (const fireName of FIRE_NAMES) {
    const ignitionMs = fireInfo[fireName].ignition.getTime();
    const fireRows = timeseriesRows.filter(row => row.fire === fireName);
    const points = fireRows.map(row => {
      const time = new Date(row.time);
      return {
        time: time,
        hours: (time.getTime() - ignitionMs) / HOUR_MS,
        frpSmooth: +row.frp_smooth,
        pixelCount: +row.pixel_count
      };
    });
    points.sort((a, b) => a.time - b.time);
    seriesByFire[fireName] = points;
  }

  const namedDetections = detections.filter(d => FIRE_NAMES.includes(d.fire));
  const maxAlignedHours = d3.max(namedDetections, d => d.hoursSinceIgnition);
  alignedSteps = d3.range(0, maxAlignedHours + ALIGNED_STEP_HOURS, ALIGNED_STEP_HOURS);

  winds = windRows.map(row => {
    const speed = +row.speed_ms;
    const fromRadians = (+row.direction_from_deg * Math.PI) / 180;
    const time = new Date(row.time);
    return {
      time: time,
      hourMs: Math.floor(time.getTime() / HOUR_MS) * HOUR_MS,
      lat: +row.lat,
      lon: +row.lon,
      speed: speed,
      directionFrom: +row.direction_from_deg,
      pressure: +row.pressure_hpa,
      east: -speed * Math.sin(fromRadians),
      north: -speed * Math.cos(fromRadians)
    };
  });

  hourlyWind = d3.rollups(winds, rows => d3.median(rows, d => d.speed), d => d.hourMs)
    .map(([hourMs, medianSpeed]) => ({ time: new Date(hourMs), medianSpeed: medianSpeed }))
    .sort((a, b) => a.time - b.time);

  const lowWindCount = winds.filter(d => d.pressure >= LOW_WIND_PRESSURE_HPA).length;
  d3.select("#wind-count-note").text(
    `The satellite can only measure wind where it sees clouds or water vapor moving. The Santa Ana air was very dry, so it found few readings. Only ${lowWindCount} of its ${winds.length} wind readings over Southern California were near the ground (an air pressure of ${LOW_WIND_PRESSURE_HPA} hPa or more). The rest were several kilometers up. The streamlines, direction marks, and compass show the general wind pattern, not the exact gusts at each fire.`
  );
}

function drawMap(counties) {
  const svg = d3.select("#map").attr("viewBox", `0 0 ${mapWidth} ${mapHeight}`);

  const regionCorners = {
    type: "MultiPoint",
    coordinates: [[MAP_REGION.west, MAP_REGION.south], [MAP_REGION.east, MAP_REGION.north]]
  };
  projection = d3.geoMercator().fitExtent([[0, 0], [mapWidth, mapHeight]], regionCorners);
  const path = d3.geoPath(projection);

  const defs = svg.append("defs");
  defs.append("clipPath").attr("id", "map-clip")
    .append("rect").attr("width", mapWidth).attr("height", mapHeight);
  defs.append("marker")
    .attr("id", "wind-arrowhead")
    .attr("viewBox", "0 0 10 10")
    .attr("refX", 8)
    .attr("refY", 5)
    .attr("markerWidth", 5)
    .attr("markerHeight", 5)
    .attr("orient", "auto")
    .append("path")
    .attr("d", "M0,0 L10,5 L0,10 z")
    .attr("fill", WIND_COLOR);
  const clippedArea = svg.append("g").attr("clip-path", "url(#map-clip)");
  clippedArea.append("rect").attr("width", mapWidth).attr("height", mapHeight).attr("fill", "#dfeaf2");
  const mapArea = clippedArea.append("g").attr("id", "zoom-layer");
  mapArea.append("g").selectAll("path")
    .data(counties.features)
    .join("path")
    .attr("class", "county")
    .attr("vector-effect", "non-scaling-stroke")
    .attr("d", path);

  mapArea.append("g").attr("id", "wind-layer");
  mapArea.append("g").attr("id", "wind-direction-layer");
  mapArea.append("g").attr("id", "pixel-layer");
  mapArea.append("g").attr("id", "active-layer");

  const leftEdge = projection([-118.422, 34.1])[0];
  const rightEdge = projection([-118.4, 34.1])[0];
  pixelSize = rightEdge - leftEdge;

  frpRadius = d3.scaleSqrt()
    .domain([0, d3.max(detections, d => d.frp)])
    .range([2, 13]);

  mapArea.append("g").selectAll("text")
    .data(referencePlaces)
    .join("text")
    .attr("class", "place-label");

  mapArea.append("g").selectAll("path")
    .data(FIRE_NAMES)
    .join("path")
    .attr("class", "ignition-star")
    .attr("d", d3.symbol(d3.symbolStar, 160))
    .attr("fill", "black")
    .attr("stroke", "white")
    .attr("stroke-width", 1.5)
    .on("mouseover", (event, d) => {
      showTooltip(event, `<strong>${d} fire started here</strong><br>${describeTime(fireInfo[d].ignition)}<br>Reported ignition point`);
    })
    .on("mousemove", moveTooltip)
    .on("mouseout", hideTooltip);

  mapArea.append("g").selectAll("text")
    .data(FIRE_NAMES)
    .join("text")
    .attr("class", "fire-name-label")
    .attr("font-weight", 700)
    .attr("fill", d => FIRE_COLORS[d])
    .attr("paint-order", "stroke")
    .attr("stroke", "white")
    .attr("pointer-events", "none")
    .text(d => `${d} fire`);

  drawPixels();
  drawLegend();
  drawWindCompass(svg);
  drawAlignedBanner(svg);
  setUpZoom(svg);
  resizeMarksForZoom();
}

function resizeMarksForZoom() {
  d3.selectAll(".place-label")
    .attr("x", d => projection([d.lon, d.lat])[0] + 4 / zoomScale)
    .attr("y", d => projection([d.lon, d.lat])[1] + 4 / zoomScale)
    .attr("font-size", 11 / zoomScale)
    .attr("stroke-width", 3 / zoomScale);

  d3.selectAll(".ignition-star")
    .attr("transform", d => {
      const [x, y] = projection([fireInfo[d].lon, fireInfo[d].lat]);
      return `translate(${x},${y}) scale(${1 / zoomScale})`;
    });

  d3.selectAll(".fire-name-label")
    .attr("x", d => projection([fireInfo[d].lon, fireInfo[d].lat])[0] + 10 / zoomScale)
    .attr("y", d => projection([fireInfo[d].lon, fireInfo[d].lat])[1] - 10 / zoomScale)
    .attr("font-size", 13 / zoomScale)
    .attr("stroke-width", 3 / zoomScale);
}

function setUpZoom(svg) {
  mapZoom = d3.zoom()
    .scaleExtent([1, 10])
    .translateExtent([[0, 0], [mapWidth, mapHeight]])
    .extent([[0, 0], [mapWidth, mapHeight]])
    .filter(event => {
      if (event.type === "wheel") {
        return event.ctrlKey || event.metaKey;
      }
      return event.button === 0 || event.type === "touchstart";
    })
    .on("zoom", event => {
      d3.select("#zoom-layer").attr("transform", event.transform);
      zoomScale = event.transform.k;
      resizeMarksForZoom();
      if (scanTimes !== undefined && alignedSteps !== undefined) {
        updateMap(currentValue());
      }
      d3.select("#zoom-level").text(`${zoomScale.toFixed(1)}×`);
    });

  svg.call(mapZoom).on("dblclick.zoom", null);
  svg.style("cursor", "grab");

  d3.select("#zoom-in").on("click", () => svg.transition().duration(350).call(mapZoom.scaleBy, 1.6));
  d3.select("#zoom-out").on("click", () => svg.transition().duration(350).call(mapZoom.scaleBy, 1 / 1.6));
  d3.select("#zoom-reset").on("click", () => svg.transition().duration(500).call(mapZoom.transform, d3.zoomIdentity));
  d3.selectAll(".zoom-to-fire").on("click", event => {
    const fireName = event.currentTarget.dataset.fire;
    const [x, y] = projection([fireInfo[fireName].lon, fireInfo[fireName].lat]);
    const zoomedIn = d3.zoomIdentity.translate(mapWidth / 2, mapHeight / 2).scale(4).translate(-x, -y);
    svg.transition().duration(700).call(mapZoom.transform, zoomedIn);
  });
}

function drawWindCompass(svg) {
  const compass = svg.append("g")
    .attr("id", "wind-compass")
    .attr("transform", `translate(${mapWidth - 108}, ${mapHeight - 126})`);
  compass.append("rect")
    .attr("x", -98)
    .attr("y", -22)
    .attr("width", 196)
    .attr("height", 138)
    .attr("rx", 6)
    .attr("fill", "white")
    .attr("opacity", 0.94)
    .attr("stroke", "#d8dce2");
  compass.append("text")
    .attr("id", "compass-title")
    .attr("x", 0)
    .attr("y", -6)
    .attr("text-anchor", "middle")
    .attr("font-size", 11)
    .attr("font-weight", 700);

  const dials = compass.selectAll(".compass-dial")
    .data([0, 1])
    .join("g")
    .attr("class", "compass-dial");
  dials.append("text")
    .attr("class", "dial-label")
    .attr("y", 10)
    .attr("text-anchor", "middle")
    .attr("font-size", 10)
    .attr("font-weight", 700);
  dials.append("circle")
    .attr("cy", 42)
    .attr("r", 24)
    .attr("fill", "none")
    .attr("stroke", "#c9ced6");
  dials.append("text")
    .attr("y", 27)
    .attr("text-anchor", "middle")
    .attr("font-size", 8)
    .attr("fill", "#5b6370")
    .text("N");
  dials.append("line")
    .attr("class", "dial-arrow")
    .attr("stroke", WIND_COLOR)
    .attr("stroke-width", 3)
    .attr("marker-end", "url(#wind-arrowhead)");
  dials.append("text")
    .attr("class", "dial-speed")
    .attr("y", 82)
    .attr("text-anchor", "middle")
    .attr("font-size", 10.5);
  dials.append("text")
    .attr("class", "dial-count")
    .attr("y", 96)
    .attr("text-anchor", "middle")
    .attr("font-size", 9.5)
    .attr("fill", "#5b6370");
}

function drawAlignedBanner(svg) {
  const banner = svg.append("g")
    .attr("id", "aligned-banner")
    .attr("transform", `translate(${mapWidth / 2}, 14)`)
    .style("display", "none");
  banner.append("rect")
    .attr("x", -230)
    .attr("y", 0)
    .attr("width", 460)
    .attr("height", 40)
    .attr("rx", 6)
    .attr("fill", "#1f2328")
    .attr("opacity", 0.88);
  banner.append("text")
    .attr("y", 16)
    .attr("text-anchor", "middle")
    .attr("font-size", 12)
    .attr("font-weight", 700)
    .attr("fill", "white")
    .text("Both fires lined up by their start times");
  banner.append("text")
    .attr("y", 31)
    .attr("text-anchor", "middle")
    .attr("font-size", 11)
    .attr("fill", "white")
    .text("Other fires and map wind barbs are hidden in this view. Choose Real time to see them.");
}

function compassName(degrees) {
  const names = ["N", "NE", "E", "SE", "S", "SW", "W", "NW"];
  return names[Math.floor(((degrees + 22.5) % 360) / 45)];
}

function windsForHour(time) {
  const hourMs = Math.floor(time.getTime() / HOUR_MS) * HOUR_MS;
  let hourWinds = winds.filter(d => d.hourMs === hourMs);
  if (state.lowWindOnly) {
    hourWinds = hourWinds.filter(d => d.pressure >= LOW_WIND_PRESSURE_HPA);
  }
  return hourWinds;
}

function setDial(dial, hourWinds, label, labelColor) {
  dial.select(".dial-label").text(label).attr("fill", labelColor);
  if (hourWinds.length === 0) {
    dial.select(".dial-arrow").attr("opacity", 0);
    dial.select(".dial-speed").text("No wind readings");
    dial.select(".dial-count").text("this hour");
    return;
  }

  const meanEast = d3.mean(hourWinds, d => d.east);
  const meanNorth = d3.mean(hourWinds, d => d.north);
  const vectorLength = Math.sqrt(meanEast * meanEast + meanNorth * meanNorth) || 1;
  const towardDegrees = ((Math.atan2(meanEast, meanNorth) * 180) / Math.PI + 360) % 360;
  const medianSpeed = d3.median(hourWinds, d => d.speed);

  dial.select(".dial-arrow")
    .attr("opacity", 1)
    .attr("x1", -(18 * meanEast) / vectorLength)
    .attr("y1", 42 + (18 * meanNorth) / vectorLength)
    .attr("x2", (18 * meanEast) / vectorLength)
    .attr("y2", 42 - (18 * meanNorth) / vectorLength);
  dial.select(".dial-speed").text(`${Math.round(medianSpeed * 2.237)} mph toward ${compassName(towardDegrees)}`);
  const readingWord = hourWinds.length === 1 ? "reading" : "readings";
  dial.select(".dial-count").text(`${Math.round(medianSpeed)} m/s, ${hourWinds.length} ${readingWord}`);
}

function updateWindCompass(value) {
  const compass = d3.select("#wind-compass");
  if (state.showWind === false || winds.length === 0) {
    compass.style("display", "none");
    return;
  }
  compass.style("display", null);

  const dials = compass.selectAll(".compass-dial");
  const firstDial = dials.filter(d => d === 0);
  const secondDial = dials.filter(d => d === 1);

  if (state.mode === "clock") {
    d3.select("#compass-title").text("Average wind (mostly high up)");
    firstDial.attr("transform", "translate(0, 0)");
    secondDial.style("display", "none");
    setDial(firstDial, windsForHour(value), "", "#1f2328");
    return;
  }

  d3.select("#compass-title").text("Wind at each fire's own time");
  firstDial.attr("transform", "translate(-48, 0)");
  secondDial.attr("transform", "translate(48, 0)").style("display", null);
  setDial(firstDial, windsForHour(fireTimeForValue("Palisades", value)), "Palisades", FIRE_COLORS.Palisades);
  setDial(secondDial, windsForHour(fireTimeForValue("Eaton", value)), "Eaton", FIRE_COLORS.Eaton);
}

function drawPixels() {
  d3.select("#pixel-layer").selectAll("rect")
    .data(pixels, d => d.id)
    .join("rect")
    .attr("x", d => projection([d.lon, d.lat])[0] - pixelSize / 2)
    .attr("y", d => projection([d.lon, d.lat])[1] - pixelSize / 2)
    .attr("width", pixelSize)
    .attr("height", pixelSize)
    .attr("fill", d => FIRE_COLORS[d.fire])
    .attr("opacity", 0)
    .on("mouseover", (event, d) => {
      const fireLabel = d.fire === "Other" ? "Other fire" : `${d.fire} fire`;
      let detailLines = "";
      if (FIRE_NAMES.includes(d.fire)) {
        const distance = distanceKm(fireInfo[d.fire].lat, fireInfo[d.fire].lon, d.lat, d.lon);
        detailLines = `<br>Reached ${describeDuration(Math.max(d.firstHours, 0))} after the fire started<br>${distance.toFixed(1)} km (${(distance * 0.621).toFixed(1)} mi) from where it started`;
      }
      showTooltip(event, `<strong>${fireLabel}</strong> (already burned)<br>Fire first seen here: ${describeTime(d.firstTime)}${detailLines}<br>Seen burning in ${d.scanCount} of the 5-minute images<br>Highest heat output here: ${d3.format(",")(Math.round(d.peakFrp))} MW`);
    })
    .on("mousemove", moveTooltip)
    .on("mouseout", hideTooltip);
}

function addLegendRow(section, drawSwatch, swatchWidth, swatchHeight, title, detail) {
  const row = section.append("div").attr("class", "legend-row");
  const swatch = row.append("svg").attr("width", swatchWidth).attr("height", swatchHeight);
  drawSwatch(swatch);
  const text = row.append("span").text(title);
  if (detail) {
    text.append("small").text(detail);
  }
}

function drawLegend() {
  const legendColors = [FIRE_COLORS.Palisades, FIRE_COLORS.Eaton, FIRE_COLORS.Other];
  const legend = d3.select("#map-legend");
  legend.selectAll("*").remove();
  legend.append("h3").text("How to read the map");

  const colorSection = legend.append("div");
  colorSection.append("h4").text("Color: which fire");
  const fireRows = [
    { title: "Palisades fire", detail: null, color: FIRE_COLORS.Palisades },
    { title: "Eaton fire", detail: null, color: FIRE_COLORS.Eaton },
    { title: "Other fires", detail: "Smaller fires nearby, such as the Hurst fire in Sylmar", color: FIRE_COLORS.Other }
  ];
  for (const fireRow of fireRows) {
    addLegendRow(colorSection, swatch => {
      swatch.append("circle").attr("cx", 9).attr("cy", 9).attr("r", 7).attr("fill", fireRow.color);
    }, 18, 18, fireRow.title, fireRow.detail);
  }

  const shapeSection = legend.append("div");
  shapeSection.append("h4").text("Shape: when");
  addLegendRow(shapeSection, swatch => {
    swatch.selectAll("rect")
      .data(legendColors)
      .join("rect")
      .attr("x", (d, index) => 1 + index * 16)
      .attr("y", 2)
      .attr("width", 14)
      .attr("height", 14)
      .attr("fill", d => d)
      .attr("opacity", 0.35);
  }, 50, 18, "Already burned", "Faded square: fire was seen in this 2 km square earlier");
  addLegendRow(shapeSection, swatch => {
    swatch.selectAll("circle")
      .data(legendColors)
      .join("circle")
      .attr("cx", (d, index) => 8 + index * 16)
      .attr("cy", 9)
      .attr("r", 7)
      .attr("fill", d => d)
      .attr("stroke", "white");
  }, 50, 18, "Burning right now", "Solid circle: fire seen here in the current 5-minute image");
  addLegendRow(shapeSection, swatch => {
    swatch.append("path")
      .attr("d", d3.symbol(d3.symbolStar, 110))
      .attr("transform", "translate(9, 9)")
      .attr("fill", "black");
  }, 50, 18, "Where the fire started", "Reported ignition point");

  const maxPower = frpRadius.domain()[1];
  const sizeValues = [
    Math.max(50, Math.round((maxPower * 0.1) / 50) * 50),
    Math.round((maxPower * 0.4) / 100) * 100,
    Math.round(maxPower / 100) * 100
  ];
  const sizeSection = legend.append("div");
  sizeSection.append("h4").text("Circle size: heat output");
  addLegendRow(sizeSection, swatch => {
    let xPosition = 0;
    for (const value of sizeValues) {
      const radius = frpRadius(value);
      swatch.append("circle")
        .attr("cx", xPosition + radius + 1)
        .attr("cy", 15)
        .attr("r", radius)
        .attr("fill", "none")
        .attr("stroke", "#5b6370");
      xPosition = xPosition + radius * 2 + 6;
    }
  }, 64, 30, sizeValues.map(value => d3.format(",")(value)).join(" / ") + " MW", "Bigger circle = more heat coming from that square");

  const windSection = legend.append("div");
  windSection.append("h4").text("Wind");
  addLegendRow(windSection, swatch => {
    swatch.append("rect")
      .attr("width", 30)
      .attr("height", 20)
      .attr("rx", 2)
      .attr("fill", "#8f9699");
    swatch.selectAll("path")
      .data([0, 1, 2])
      .join("path")
      .attr("d", (d, index) => `M1,${5 + index * 5}C10,${3 + index * 5} 15,${15 - index * 4} 27,${4 + index * 5}`)
      .attr("fill", "none")
      .attr("stroke", WIND_STREAM_COLOR)
      .attr("stroke-width", (d, index) => 0.9 + index * 0.65)
      .attr("stroke-linecap", "round");
  }, 30, 20, "Interpolated wind flow", "White curves show wind; thicker, more opaque lines are faster");
  addLegendRow(windSection, swatch => {
    swatch.append("line")
      .attr("x1", 4).attr("y1", 10).attr("x2", 25).attr("y2", 10)
      .attr("stroke", WIND_COLOR)
      .attr("stroke-width", 2);
    swatch.append("path")
      .attr("d", "M25,6L31,10L25,14Z")
      .attr("fill", WIND_COLOR);
  }, 30, 20, "Regional compass", "Arrow shows the average wind direction");
}

function updateMap(value) {
  d3.select("#pixel-layer").selectAll("rect")
    .attr("opacity", d => (pixelIsReached(d, value) ? 0.35 : 0))
    .attr("pointer-events", d => (pixelIsReached(d, value) ? "all" : "none"));

  const activeDetections = detections.filter(d => detectionIsActive(d, value));
  activeDetections.sort((a, b) => b.frp - a.frp);
  activeTotals = {};
  for (const detection of activeDetections) {
    activeTotals[detection.fire] = (activeTotals[detection.fire] || 0) + detection.frp;
  }

  d3.select("#active-layer").selectAll("circle")
    .data(activeDetections, d => `${d.fire}|${d.pixelKey}`)
    .join("circle")
    .attr("cx", d => projection([d.lon, d.lat])[0])
    .attr("cy", d => projection([d.lon, d.lat])[1])
    .attr("r", d => frpRadius(d.frp) / zoomScale)
    .attr("fill", d => FIRE_COLORS[d.fire])
    .attr("fill-opacity", 0.85)
    .attr("stroke", "white")
    .attr("stroke-width", 0.8 / zoomScale)
    .on("mouseover", (event, d) => {
      const fireLabel = d.fire === "Other" ? "Other fire" : `${d.fire} fire`;
      const temperatureText = d.temp === null ? "not reported" : `${Math.round(d.temp)} K (${Math.round((d.temp - 273.15) * 1.8 + 32)} °F)`;
      let detailLines = "";
      if (FIRE_NAMES.includes(d.fire)) {
        const share = activeTotals[d.fire] > 0 ? Math.round((100 * d.frp) / activeTotals[d.fire]) : 0;
        const distance = distanceKm(fireInfo[d.fire].lat, fireInfo[d.fire].lon, d.lat, d.lon);
        detailLines = `<br>${share}% of the ${d.fire} fire's heat in this image<br>${distance.toFixed(1)} km (${(distance * 0.621).toFixed(1)} mi) from where it started<br>Fire burning for ${describeDuration(d.hoursSinceIgnition)}`;
      }
      showTooltip(event, `<strong>${fireLabel}</strong> (burning now)<br>${describeTime(d.time)}<br>Heat output in this square: ${d3.format(",")(Math.round(d.frp))} MW<br>Estimated fire temperature: ${temperatureText}${detailLines}`);
    })
    .on("mousemove", moveTooltip)
    .on("mouseout", hideTooltip);

  updateWind(value);
}

function updateWind(value) {
  let visibleWinds = [];
  let noteText = "";

  if (state.showWind === false) {
    noteText = "";
  } else if (winds.length === 0) {
    noteText = "No satellite wind vectors were available for this window.";
  } else if (state.mode === "aligned") {
    noteText = "The fires are lined up by their start times, so the map cannot show one moment of wind. The compass shows each fire's regional wind; map flow lines appear only in Real time.";
  } else {
    visibleWinds = windsForHour(value);
    const insideMap = visibleWinds.filter(d => d.lon >= MAP_REGION.west && d.lon <= MAP_REGION.east && d.lat >= MAP_REGION.south && d.lat <= MAP_REGION.north);
    noteText = `${insideMap.length} wind readings over this map area this hour. Flow direction is interpolated from nearby satellite readings; the gentle meander is visual styling. Thicker, more opaque lines indicate faster wind, and lines fade where measurements are sparse.`;
    if (insideMap.length === 0) {
      noteText = "No direct wind readings over this map area this hour. Any visible flow lines are interpolated from nearby satellite samples and fade where measurements are sparse.";
    }
  }

  d3.select("#wind-note").text(noteText);
  d3.select("#aligned-banner").style("display", state.mode === "aligned" ? null : "none");
  updateWindCompass(value);

  const streamKey = state.showWind && state.mode === "clock"
    ? `${Math.floor(value.getTime() / HOUR_MS)}|${state.lowWindOnly}`
    : null;
  if (streamKey !== windStreamCacheKey) {
    windStreamCacheKey = streamKey;
    windStreamCache = streamKey === null ? [] : createWindStreamlines(visibleWinds);
  }

  d3.select("#wind-layer").selectAll("path")
    .data(windStreamCache, d => d.id)
    .join("path")
    .attr("class", "wind-streamline")
    .attr("d", d => windStreamLine(d.points))
    .attr("fill", "none")
    .attr("stroke", WIND_STREAM_COLOR)
    .attr("stroke-width", d => (0.55 + Math.min(d.speed, 25) / 22) * (d.nearGround ? 1.15 : 1))
    .attr("vector-effect", "non-scaling-stroke")
    .attr("stroke-linecap", "round")
    .attr("opacity", d => (0.38 + Math.min(d.speed / 20, 1) * 0.22) * (d.nearGround ? 1 : 0.82))
    .attr("pointer-events", "none");

  const directionMarks = windStreamCache.flatMap((streamline, index) => {
    if (index % 5 !== 0 || streamline.points.length < 12) {
      return [];
    }
    return [0.38, 0.68].map(fraction => {
      const pointIndex = Math.round((streamline.points.length - 1) * fraction);
      const before = streamline.points[pointIndex - 1];
      const point = streamline.points[pointIndex];
      const after = streamline.points[pointIndex + 1];
      const angle = Math.atan2(after.y - before.y, after.x - before.x) * (180 / Math.PI);
      return { id: `${streamline.id}|${fraction}`, x: point.x, y: point.y, angle: angle };
    });
  });

  d3.select("#wind-direction-layer").selectAll("path")
    .data(directionMarks, d => d.id)
    .join("path")
    .attr("class", "wind-direction-mark")
    .attr("d", "M-3.5,-2.5L4,0L-3.5,2.5Z")
    .attr("transform", d => `translate(${d.x},${d.y}) rotate(${d.angle}) scale(${1 / zoomScale})`)
    .attr("pointer-events", "none");
}

function drawCharts() {
  drawPowerChart();
  drawWindChart();
}

function drawPowerChart() {
  const svg = d3.select("#power-chart").attr("viewBox", `0 0 ${chartWidth} ${powerChartHeight}`);
  svg.selectAll("*").remove();
  const innerWidth = chartWidth - chartMargin.left - chartMargin.right;
  const innerHeight = powerChartHeight - chartMargin.top - chartMargin.bottom;
  const chartArea = svg.append("g").attr("transform", `translate(${chartMargin.left},${chartMargin.top})`);

  let xScale;
  let xAxis;
  let linePoints = {};

  if (state.mode === "clock") {
    xScale = d3.scaleUtc()
      .domain([toPacific(scanTimes[0]), toPacific(scanTimes[scanTimes.length - 1])])
      .range([0, innerWidth]);
    xAxis = d3.axisBottom(xScale).ticks(8).tickFormat(d3.utcFormat("%a %-I %p"));
    for (const fireName of FIRE_NAMES) {
      linePoints[fireName] = seriesByFire[fireName].map(point => ({ x: toPacific(point.time), y: point.frpSmooth }));
    }
    d3.select("#power-chart-title").text("Fire power over time: how much heat each fire gave off");
    d3.select("#power-chart-caption").text("Total heat output of each fire in megawatts, averaged over 30 minutes. Dashed lines mark when each fire started, and the black line marks the time on the slider. Click or drag on the chart to move through time.");
  } else {
    xScale = d3.scaleLinear()
      .domain([0, alignedSteps[alignedSteps.length - 1]])
      .range([0, innerWidth]);
    xAxis = d3.axisBottom(xScale).ticks(10).tickFormat(d => `${d} h`);
    for (const fireName of FIRE_NAMES) {
      const afterIgnition = seriesByFire[fireName].filter(point => point.hours >= 0);
      linePoints[fireName] = afterIgnition.map(point => ({ x: point.hours, y: point.frpSmooth }));
    }
    d3.select("#power-chart-title").text("Fire power, lined up from when each fire started");
    d3.select("#power-chart-caption").text("0 h is the moment each fire started, so both fires can be compared at the same age. Heat output in megawatts, averaged over 30 minutes. Click or drag on the chart to move through time.");
  }

  const maxPower = d3.max(FIRE_NAMES, fireName => d3.max(seriesByFire[fireName], point => point.frpSmooth));
  const yScale = d3.scaleLinear().domain([0, maxPower]).nice().range([innerHeight, 0]);

  chartArea.append("g")
    .attr("class", "axis")
    .attr("transform", `translate(0,${innerHeight})`)
    .call(xAxis);
  chartArea.append("g")
    .attr("class", "axis")
    .call(d3.axisLeft(yScale).ticks(5).tickFormat(d3.format(",")));
  chartArea.append("text")
    .attr("class", "chart-label")
    .attr("transform", "rotate(-90)")
    .attr("x", -innerHeight / 2)
    .attr("y", -50)
    .attr("text-anchor", "middle")
    .text("Heat output (MW)");

  if (state.mode === "clock") {
    chartArea.selectAll(".ignition-line")
      .data(FIRE_NAMES)
      .join("line")
      .attr("class", "ignition-line")
      .attr("x1", d => xScale(toPacific(fireInfo[d].ignition)))
      .attr("x2", d => xScale(toPacific(fireInfo[d].ignition)))
      .attr("y1", 0)
      .attr("y2", innerHeight)
      .attr("stroke", d => FIRE_COLORS[d])
      .attr("stroke-dasharray", "4 3");
    chartArea.selectAll(".ignition-label")
      .data(FIRE_NAMES)
      .join("text")
      .attr("class", "chart-label")
      .attr("x", d => xScale(toPacific(fireInfo[d].ignition)) + 4)
      .attr("y", 10)
      .text(d => `${d} starts`);
  }

  const line = d3.line().x(d => xScale(d.x)).y(d => yScale(d.y));
  chartArea.selectAll(".power-line")
    .data(FIRE_NAMES)
    .join("path")
    .attr("class", "power-line")
    .attr("fill", "none")
    .attr("stroke", d => FIRE_COLORS[d])
    .attr("stroke-width", 2)
    .attr("d", d => line(linePoints[d]));

  chartArea.selectAll(".line-label")
    .data(FIRE_NAMES)
    .join("text")
    .attr("class", "line-label")
    .attr("x", innerWidth - 4)
    .attr("y", (d, index) => 12 + index * 16)
    .attr("text-anchor", "end")
    .attr("font-size", 12)
    .attr("font-weight", 700)
    .attr("fill", d => FIRE_COLORS[d])
    .text(d => d);

  const marker = chartArea.append("line")
    .attr("y1", 0)
    .attr("y2", innerHeight)
    .attr("stroke", "#1f2328")
    .attr("stroke-width", 1.5);

  const hoverLine = chartArea.append("line")
    .attr("y1", 0)
    .attr("y2", innerHeight)
    .attr("stroke", "#8a919c")
    .attr("stroke-dasharray", "2 3")
    .attr("opacity", 0);

  chartArea.append("rect")
    .attr("width", innerWidth)
    .attr("height", innerHeight)
    .attr("fill", "transparent")
    .style("cursor", "pointer")
    .on("pointerdown", event => scrubChart(event, xScale))
    .on("pointermove", event => {
      if (event.buttons === 1) {
        scrubChart(event, xScale);
      }
      const [mouseX] = d3.pointer(event);
      hoverLine.attr("x1", mouseX).attr("x2", mouseX).attr("opacity", 1);
      showTooltip(event, describeChartPoint(xScale.invert(mouseX)));
    })
    .on("pointerleave", () => {
      hoverLine.attr("opacity", 0);
      hideTooltip();
    });

  chartScales.powerX = xScale;
  chartScales.powerMarker = marker;
}

function drawWindChart() {
  const block = d3.select("#wind-chart-block");
  const svg = d3.select("#wind-chart").attr("viewBox", `0 0 ${chartWidth} ${windChartHeight}`);
  svg.selectAll("*").remove();
  chartScales.windMarker = null;

  if (state.mode === "aligned" || hourlyWind.length === 0) {
    block.style("display", "none");
    return;
  }
  block.style("display", null);

  const innerWidth = chartWidth - chartMargin.left - chartMargin.right;
  const innerHeight = windChartHeight - chartMargin.top - chartMargin.bottom;
  const chartArea = svg.append("g").attr("transform", `translate(${chartMargin.left},${chartMargin.top})`);

  const xScale = chartScales.powerX;
  const yScale = d3.scaleLinear()
    .domain([0, d3.max(hourlyWind, d => d.medianSpeed)])
    .nice()
    .range([innerHeight, 0]);

  chartArea.append("g")
    .attr("class", "axis")
    .attr("transform", `translate(0,${innerHeight})`)
    .call(d3.axisBottom(xScale).ticks(8).tickFormat(d3.utcFormat("%a %-I %p")));
  chartArea.append("g")
    .attr("class", "axis")
    .call(d3.axisLeft(yScale).ticks(3));
  chartArea.append("text")
    .attr("class", "chart-label")
    .attr("transform", "rotate(-90)")
    .attr("x", -innerHeight / 2)
    .attr("y", -50)
    .attr("text-anchor", "middle")
    .text("Wind (m/s)");

  const line = d3.line()
    .x(d => xScale(toPacific(new Date(d.time.getTime() + HOUR_MS / 2))))
    .y(d => yScale(d.medianSpeed));
  chartArea.append("path")
    .datum(hourlyWind)
    .attr("fill", "none")
    .attr("stroke", WIND_COLOR)
    .attr("stroke-width", 2)
    .attr("d", line);
  chartArea.selectAll(".wind-point")
    .data(hourlyWind)
    .join("circle")
    .attr("class", "wind-point")
    .attr("cx", d => xScale(toPacific(new Date(d.time.getTime() + HOUR_MS / 2))))
    .attr("cy", d => yScale(d.medianSpeed))
    .attr("r", 2.5)
    .attr("fill", WIND_COLOR);

  chartScales.windMarker = chartArea.append("line")
    .attr("y1", 0)
    .attr("y2", innerHeight)
    .attr("stroke", "#1f2328")
    .attr("stroke-width", 1.5);

  chartArea.append("rect")
    .attr("width", innerWidth)
    .attr("height", innerHeight)
    .attr("fill", "transparent")
    .style("cursor", "pointer")
    .on("pointerdown", event => scrubChart(event, xScale))
    .on("pointermove", event => {
      if (event.buttons === 1) {
        scrubChart(event, xScale);
      }
    });
}

function describeChartPoint(chosen) {
  let heading;
  const lines = [];
  for (const fireName of FIRE_NAMES) {
    const series = seriesByFire[fireName];
    let point;
    if (state.mode === "clock") {
      const utcTime = new Date(chosen.getTime() + PACIFIC_OFFSET_MS);
      point = series[nearestIndex(series.map(entry => entry.time), utcTime)];
      heading = describeTime(point.time);
    } else {
      point = series[nearestIndex(series.map(entry => entry.hours), chosen)];
      heading = `${describeDuration(Math.max(chosen, 0))} after each fire started`;
    }
    let valueText = `${d3.format(",")(Math.round(point.frpSmooth))} MW`;
    if (point.hours < 0) {
      valueText = "not started yet";
    }
    lines.push(`<span style="color: ${FIRE_COLORS[fireName]}; font-weight: 700">${fireName}:</span> ${valueText}`);
  }
  return `<strong>${heading}</strong><br>${lines.join("<br>")}<br><em>Click to move the map here</em>`;
}

function scrubChart(event, xScale) {
  const [mouseX] = d3.pointer(event);
  const chosen = xScale.invert(mouseX);
  if (state.mode === "clock") {
    const utcTime = new Date(chosen.getTime() + PACIFIC_OFFSET_MS);
    state.stepIndex = nearestIndex(scanTimes, utcTime);
  } else {
    state.stepIndex = nearestIndex(alignedSteps, chosen);
  }
  render();
}

function updateCharts(value) {
  let markerX;
  if (state.mode === "clock") {
    markerX = chartScales.powerX(toPacific(value));
  } else {
    markerX = chartScales.powerX(value);
  }
  chartScales.powerMarker.attr("x1", markerX).attr("x2", markerX);
  if (chartScales.windMarker !== null) {
    chartScales.windMarker.attr("x1", markerX).attr("x2", markerX);
  }
}

function updateReadout(value) {
  const cards = FIRE_NAMES.map(fireName => {
    const fireTime = fireTimeForValue(fireName, value);
    const ignition = fireInfo[fireName].ignition;
    const hoursBurning = (fireTime.getTime() - ignition.getTime()) / HOUR_MS;
    const series = seriesByFire[fireName];
    const seriesTimes = series.map(point => point.time);
    const nearestPoint = series[nearestIndex(seriesTimes, fireTime)];
    const pointsSoFar = series.filter(point => point.time <= fireTime && point.hours >= 0);
    const peakSoFar = pointsSoFar.length > 0 ? d3.max(pointsSoFar, point => point.frpSmooth) : 0;
    const pixelsReached = pixels.filter(pixel => pixel.fire === fireName && pixel.firstTime <= fireTime).length;

    let status = `Burning for ${describeDuration(hoursBurning)}`;
    if (hoursBurning < 0) {
      status = `Starts in ${describeDuration(-hoursBurning)}`;
    }
    const outsideWindow = fireTime > scanTimes[scanTimes.length - 1];

    return {
      fireName: fireName,
      status: status,
      fireTimeText: describeTime(fireTime),
      powerNow: hoursBurning < 0 ? "Not started" : outsideWindow ? "No data" : `${d3.format(",")(Math.round(nearestPoint.frpSmooth))} MW`,
      peakSoFar: hoursBurning < 0 ? "Not started" : `${d3.format(",")(Math.round(peakSoFar))} MW`,
      pixelsReached: pixelsReached
    };
  });

  d3.select("#readout").selectAll(".fire-card")
    .data(cards, d => d.fireName)
    .join(enter => {
      const card = enter.append("div").attr("class", "fire-card");
      card.style("border-left-color", d => FIRE_COLORS[d.fireName]);
      card.append("h3").style("color", d => FIRE_COLORS[d.fireName]).text(d => `${d.fireName} fire`);
      card.append("p").attr("class", "status");
      const list = card.append("dl");
      list.append("dt").text("Clock time");
      list.append("dd").attr("class", "clock-time");
      list.append("dt").text("Heat output right now");
      list.append("dd").attr("class", "power-now");
      list.append("dt").text("Highest heat output so far");
      list.append("dd").attr("class", "peak-so-far");
      list.append("dt").text("2 km squares reached so far");
      list.append("dd").attr("class", "pixels-reached");
      return card;
    })
    .call(card => {
      card.select(".status").text(d => d.status);
      card.select(".clock-time").text(d => d.fireTimeText);
      card.select(".power-now").text(d => d.powerNow);
      card.select(".peak-so-far").text(d => d.peakSoFar);
      card.select(".pixels-reached").text(d => d.pixelsReached);
    });
}

function updateTimeLabel(value) {
  let labelText;
  if (state.mode === "clock") {
    labelText = describeTime(value);
  } else {
    labelText = `${describeDuration(value)} after each fire started`;
  }
  d3.select("#time-label").text(labelText);
}

function render() {
  const value = currentValue();
  d3.select("#time-slider").property("value", state.stepIndex);
  updateTimeLabel(value);
  updateMap(value);
  updateCharts(value);
  updateReadout(value);
}

function resetForMode() {
  stopPlaying();
  d3.select("#time-slider").attr("max", currentSteps().length - 1);
  state.stepIndex = Math.min(state.stepIndex, currentSteps().length - 1);
  drawCharts();
  render();
}

function drawKeyMoments() {
  const moments = [];
  for (const fireName of FIRE_NAMES) {
    moments.push({ label: `${fireName} starts`, time: fireInfo[fireName].ignition });
  }
  if (hourlyWind.length > 0) {
    const windiestHour = d3.greatest(hourlyWind, d => d.medianSpeed);
    moments.push({ label: `Strongest winds (${formatPacificHour(toPacific(windiestHour.time))})`, time: windiestHour.time });
  }
  for (const fireName of FIRE_NAMES) {
    const peakPoint = d3.greatest(seriesByFire[fireName], point => point.frpSmooth);
    moments.push({ label: `${fireName} peak`, time: peakPoint.time });
  }
  moments.sort((a, b) => a.time - b.time);

  d3.select("#key-moments").selectAll("button")
    .data(moments)
    .join("button")
    .attr("type", "button")
    .text(d => d.label)
    .on("click", (event, d) => jumpToTime(d.time));
}

function setMode(mode) {
  state.mode = mode;
  d3.selectAll("input[name='mode']").property("checked", function () {
    return this.value === mode;
  });
}

function scrollToMap() {
  document.querySelector(".controls").scrollIntoView({ behavior: "smooth", block: "start" });
}

function jumpToTime(time) {
  stopPlaying();
  if (state.mode !== "clock") {
    setMode("clock");
    state.stepIndex = nearestIndex(scanTimes, time);
    resetForMode();
  } else {
    state.stepIndex = nearestIndex(scanTimes, time);
    render();
  }
}

function jumpToAlignedHours(hours) {
  stopPlaying();
  if (state.mode !== "aligned") {
    setMode("aligned");
    state.stepIndex = nearestIndex(alignedSteps, hours);
    resetForMode();
  } else {
    state.stepIndex = nearestIndex(alignedSteps, hours);
    render();
  }
}

function medianWindAt(time) {
  const hourMs = Math.floor(time.getTime() / HOUR_MS) * HOUR_MS;
  const hourWinds = winds.filter(d => d.hourMs === hourMs);
  if (hourWinds.length === 0) {
    return null;
  }
  return d3.median(hourWinds, d => d.speed);
}

function drawFindings() {
  const findings = [];

  const peaks = FIRE_NAMES.map(fireName => {
    const afterIgnition = seriesByFire[fireName].filter(point => point.hours >= 0);
    const peakPoint = d3.greatest(afterIgnition, point => point.frpSmooth);
    return { fireName: fireName, power: peakPoint.frpSmooth, time: peakPoint.time };
  });
  peaks.sort((a, b) => b.power - a.power);
  const strongerPeak = peaks[0];
  const weakerPeak = peaks[1];
  const peakRatio = strongerPeak.power / weakerPeak.power;
  let intensityPhrase = "burned much more intensely";
  if (peakRatio < 1.5) {
    intensityPhrase = "burned somewhat more intensely";
  }
  if (peakRatio < 1.15) {
    intensityPhrase = "reached about the same peak intensity as the other fire";
  }
  findings.push({
    html: `${fireLabelHtml(strongerPeak.fireName)} ${intensityPhrase}. Its heat output peaked at <strong>${d3.format(",")(Math.round(strongerPeak.power))} MW</strong> (${describeTime(strongerPeak.time)}), about <strong>${peakRatio.toFixed(1)} times</strong> <strong style="color: ${FIRE_COLORS[weakerPeak.fireName]}">${possessive(weakerPeak.fireName)}</strong> peak of ${d3.format(",")(Math.round(weakerPeak.power))} MW.`,
    buttonText: `Show me the ${strongerPeak.fireName} peak`,
    action: () => jumpToTime(strongerPeak.time)
  });

  const earlyHours = 12;
  const earlySquares = FIRE_NAMES.map(fireName => ({
    fireName: fireName,
    count: pixels.filter(pixel => pixel.fire === fireName && pixel.firstHours !== null && pixel.firstHours <= earlyHours).length
  }));
  earlySquares.sort((a, b) => b.count - a.count);
  const intenseFire = strongerPeak.fireName;
  let spreadSentence = `${fireLabelHtml(earlySquares[0].fireName)} covered more ground early.`;
  if (earlySquares[0].fireName === intenseFire && peakRatio >= 1.15) {
    spreadSentence = `${fireLabelHtml(earlySquares[0].fireName)} covered more ground early and also burned hotter.`;
  }
  if (earlySquares[0].fireName !== intenseFire && peakRatio >= 1.15) {
    spreadSentence = `So ${fireLabelHtml(earlySquares[0].fireName)} spread over more ground early, even though ${fireLabelHtml(intenseFire)} burned hotter.`;
  }
  findings.push({
    html: `In the first ${earlyHours} hours after each fire started, ${fireLabelHtml(earlySquares[0].fireName)} reached <strong>${earlySquares[0].count}</strong> of the satellite's 2 km squares and ${fireLabelHtml(earlySquares[1].fireName)} reached <strong>${earlySquares[1].count}</strong>. ${spreadSentence}`,
    buttonText: `Show me both fires at ${earlyHours} hours`,
    action: () => jumpToAlignedHours(earlyHours)
  });

  if (hourlyWind.length > 0) {
    const windAtStart = FIRE_NAMES.map(fireName => ({ fireName: fireName, speed: medianWindAt(fireInfo[fireName].ignition) }));
    const startTexts = windAtStart
      .filter(entry => entry.speed !== null)
      .map(entry => `${describeSpeed(entry.speed)} when ${fireLabelHtml(entry.fireName)} started`);
    const windiestHour = d3.greatest(hourlyWind, d => d.medianSpeed);
    const windiestLocal = toPacific(windiestHour.time);
    let windHtml = `The strongest satellite winds came around <strong>${d3.utcFormat("%-I %p")(windiestLocal)} PST on ${d3.utcFormat("%A, %B %-d")(windiestLocal)}</strong>, at about ${describeSpeed(windiestHour.medianSpeed)}.`;
    if (startTexts.length > 0) {
      windHtml = `${windHtml} The typical wind was ${startTexts.join(" and ")}.`;
    }
    findings.push({
      html: `${windHtml} Most readings were high above the ground, so these show the overall wind event, not surface gusts.`,
      buttonText: "Show me the strongest winds",
      action: () => jumpToTime(windiestHour.time)
    });
  }

  const hoursBetween = (fireInfo.Eaton.ignition - fireInfo.Palisades.ignition) / HOUR_MS;
  findings.push({
    html: `${fireLabelHtml("Eaton")} started about <strong>${describeDuration(hoursBetween)}</strong> after ${fireLabelHtml("Palisades")}, so for most of the evening both fires were burning at the same time under the same wind event.`,
    buttonText: "Show me when Eaton started",
    action: () => jumpToTime(fireInfo.Eaton.ignition)
  });

  const items = d3.select("#findings-list").selectAll("li")
    .data(findings)
    .join("li");
  items.append("span").attr("class", "finding-text").html(d => d.html);
  items.append("button")
    .attr("type", "button")
    .text(d => d.buttonText)
    .on("click", (event, d) => {
      d.action();
      scrollToMap();
    });
}

function stopPlaying() {
  if (state.playTimer !== null) {
    state.playTimer.stop();
    state.playTimer = null;
  }
  d3.select("#play-button").text("Play");
}

function startPlaying() {
  if (state.stepIndex >= currentSteps().length - 1) {
    state.stepIndex = 0;
  }
  d3.select("#play-button").text("Pause");
  state.playTimer = d3.interval(() => {
    if (state.stepIndex >= currentSteps().length - 1) {
      stopPlaying();
      return;
    }
    state.stepIndex = state.stepIndex + 1;
    render();
  }, PLAY_INTERVAL_MS);
}

function setUpControls() {
  d3.select("#time-slider").on("input", event => {
    stopPlaying();
    state.stepIndex = +event.target.value;
    render();
  });

  d3.select("#play-button").on("click", () => {
    if (state.playTimer !== null) {
      stopPlaying();
    } else {
      startPlaying();
    }
  });

  d3.selectAll("input[name='mode']").on("change", event => {
    state.mode = event.target.value;
    state.stepIndex = 0;
    resetForMode();
  });

  d3.select("#show-wind").on("change", event => {
    state.showWind = event.target.checked;
    d3.select("#low-wind-only").property("disabled", state.showWind === false);
    render();
  });

  d3.select("#low-wind-only").on("change", event => {
    state.lowWindOnly = event.target.checked;
    render();
  });
}

function showTooltip(event, html) {
  tooltip.style("opacity", 1).html(html);
  moveTooltip(event);
}

function moveTooltip(event) {
  const tooltipWidth = tooltip.node().offsetWidth;
  let left = event.pageX + 14;
  if (left + tooltipWidth > window.scrollX + window.innerWidth - 8) {
    left = event.pageX - tooltipWidth - 14;
  }
  tooltip.style("left", `${Math.max(left, 0)}px`).style("top", `${event.pageY - 18}px`);
}

function hideTooltip() {
  tooltip.style("opacity", 0).style("left", "0px").style("top", "0px");
}