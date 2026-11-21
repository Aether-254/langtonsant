import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1935 : checkSingleBlackFast (-68, -45) 14783 .west (21, 31) (-50, 11) = true := by
  decide +kernel

end LangtonsAnt
