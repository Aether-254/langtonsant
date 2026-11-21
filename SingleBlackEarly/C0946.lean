import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0946 : checkSingleBlackFast (20, 9) 26075 .east (-14, 7) (-32, -34) = true := by
  decide +kernel

end LangtonsAnt
