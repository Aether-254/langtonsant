import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0080 : checkSingleBlackFast (5, -5) 2811 .west (-4, 2) (-17, -6) = true := by
  decide +kernel

end LangtonsAnt
