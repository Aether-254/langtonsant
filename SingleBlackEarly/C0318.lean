import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0318 : checkSingleBlackFast (1, 12) 5343 .west (-9, -5) (-16, -9) = true := by
  decide +kernel

end LangtonsAnt
