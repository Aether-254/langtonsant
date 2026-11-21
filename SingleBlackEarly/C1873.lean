import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1873 : checkSingleBlackFast (-63, -39) 14575 .west (18, 29) (-48, 10) = true := by
  decide +kernel

end LangtonsAnt
