import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0692 : checkSingleBlackFast (20, -10) 5901 .west (-13, 4) (-18, -14) = true := by
  decide +kernel

end LangtonsAnt
