import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0317 : checkSingleBlackFast (0, 12) 4847 .west (-12, 1) (-16, -14) = true := by
  decide +kernel

end LangtonsAnt
