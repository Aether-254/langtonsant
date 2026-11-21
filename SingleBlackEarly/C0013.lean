import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0013 : checkSingleBlackFast (-1, -2) 1957 .west (-2, 6) (-12, -7) = true := by
  decide +kernel

end LangtonsAnt
