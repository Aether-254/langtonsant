import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1493 : checkSingleBlackFast (-28, -3) 25108 .south (-4, -6) (-18, -20) = true := by
  decide +kernel

end LangtonsAnt
