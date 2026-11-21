import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1622 : checkSingleBlackFast (-41, -14) 26016 .north (4, 11) (-12, -39) = true := by
  decide +kernel

end LangtonsAnt
