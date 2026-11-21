import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0466 : checkSingleBlackFast2 (16, 14) 12122 .south (-4, -11) (-27, -8) = true := by
  decide +kernel

end LangtonsAnt
